# Full Classical Linear Type Theory
This was intended as a message for the [r/PLs Discord](https://proglangdesign.net), but it was too long to post. You can share it if you'd like, but this wasn't written as an article, so:
* it has not been edited or proven,
* it isn't explained very well either, and
* the explanation is based on my intuition so it's not much of a tutorial, so
* overall, it might not be helpful to anyone else.

## Background

I think I finally understand how to implement full classical linear type theory. Still need to actually write the code, but it's the most promising approach I've found so far.

I was trying to design an IR for a language which imposes as few constraints on memory layout as possible without requiring implicit memory allocation. That problem is still open, but it specifically got me working on linear languages written in imperative style rather than as expressions, which is enlightening.

Note that by duality, propositions on the RHS correspond with dual propositions on the LHS, i.e. arguments with a negative type. I found it less confusing to only think about arguments instead of the mysterious RHS. So the way an "expression" is written, it doesn't actually "return" anything. Its goal is to continue shrinking the arguments until it has consumed all of them and there are none left. (However, if you imagine all variables with of type ¬A as a variable of type A in a distinct right context, it still works.)

Notationally, assignment operators `w , x := foo y z` defines variables `w , x` and consumes variables `y , z`, erasing them from the context. On the other hand, operators without `:=` are control flow operators. Note that because there is no such thing as return values, you cannot "return" a value from a control flow block. So if a branch introduces a variable `x : A`, `x` must be consumed by that branch before continuing. (This is necessary to prevent paradoxes and computation getting stuck due to LEM.)

Match blocks using `[` are additive and both branches must consume exactly the same portion of the context. Match blocks using `{` are multiplicative, and both branches must consume entirely disjoint portions of the context.

An expression is finished when there are no variables remaining in the context. Note that the types on the left hand side of an assignment or branch are always smaller than the types they match against; this is how we guarantee that computations make progress.

## Explanation

Here are the primitive operators:
```
-- refine a hole of type ¬(A ⊕ B) to a hole of type ¬A
(x : ¬A) := inj₁ (w : ¬(A ⊕ B))
(y : ¬B) := inj₂ (w : ¬(A ⊕ B))
match (w : A ⊕ B) [
  (x : A) => ...
  (y : B) => ...
]
-- immediately consumes the entire context; this is necessarily the last statement in the expression.
absurd (x : 0)

(x : A) := proj₁ (w : A & B)
(y : B) := proj₂ (w : A & B)
-- refine a hole of type ¬(A & B) to a hole of type ¬A and a hole of type ¬B
match (w : ¬(A & B)) [
  (x : ¬A) => ...
  (y : ¬B) => ...
]
-- same as absurd
forget (x : ¬⊤)

(x : A) , (y : B) := w : A ⊗ B
match (w : ¬(A ⊗ B)) {
  (x : ¬A) => ...
  (y : ¬B) => ...
}
-- remove variables from the context; do not create any new variables.
:= drop (x : 1)
:= unit (x : ¬1)

(x : ¬A) , (y : ¬B) := w : ¬(A ⅋ B)
match (w : A ⅋ B) {
  (x : A) => ...
  (y : B) => ...
}
satisfy (x : ¬⊥)
finish (x : ⊥)

lem {
  (f : ¬A) => ...
  (x : A) => ...
}
:= app (f : ¬A) (x : A)
```
LEM is how you can construct a value whose constructors operate on negative types, e.g.
```
lem {
  (x : ¬(1 ⊕ 1)) {
    x' := inj₂ x
    := unit x'
  }
  (x : (1 ⊕ 1)) {
    -- do stuff with your new value...
  }
}
```

I haven't written down the rules for exponentials yet, but I expect that they'd work similarly. Expressing the constraints on they impose on the context would be awkward, but there's some hope that there'd be a nice syntactic way to represent them.

Semantically, it works like this: you have a bunch of coroutines. The coroutines may be implemented in terms of continuations in a single thread, or in terms of message passing between multiple threads via typed channels.

Suppose you're executing an expression. You do so by sequentially executing each statement. There are a bunch of variables in the context. Each variable is a channel which you can use to send messages to other coroutines.

When you encounter an assignment, you send a message to the coroutine who owns the variable corresponding with the operation you used. "Please send me the first projection." or "I am sending you the first injection." "I am splitting the pair into two. When I use each half, I will ask you to compute the corresponding half."

When you encounter a match, you await a message from the coroutine who owns the variable. "Which injection are you sending me?" "Which argument of the pair would you like me to compute?"

The coroutine is blocked while awaiting the message, so you continue executing other coroutines instead. The coroutines can't get stuck because a coroutine can never await its own variable. All operators in expressions can only make variables *smaller*, never create a new variable. The only way to create a new variable is with `lem` (both branches of which compute in parallel), but the variables are stuck in separate match arms (and can't be returned, so you can't bring them back together again), so whenever you block on one match arm, you simply jump to the other, and the computation is forced to make progress.

## Future Work
I hope to follow this up by actually implementing it, so hopefully it'll actually work, and hopefully I'll be able to actually prove that this is classical linear type theory and not some meaningless bullshit (i.e. "intuitionistic linear type theory plus coroutines").
* you could also add an additional intuitionistic context with structural rules, which makes `!` redundant (at least the full version, not the [soft version](https://ncatlab.org/nlab/show/soft+linear+logic). (You can avoid the weird constraints `!` imposes on the context by replacing the introduction rule with any term of linear type `¬A ⊢` which only depends on the intuitionistic context; the other rules may be replaced with variable references to the intuitionistic context.)
* This context may also be dependent, where the dependent context is used to construct linear computations (which are embedded back in to the dependent context as described above).
* I don't know what a cointuitionistic context or "co-dependent" context would look like (or both?) but it'd be interesting to find out.
* Restricting this to basic logic or dual intuitionistic logic may yield something useful...? Also restrictions to information-conserving versions.
* Trying to add effects and coeffects to the system, and considering how it works with partial functions, which is part of why I was interested in linear stuff in the first place (i.e. relationship to CPBV/fire triangle).
* generalize this method to non-linear stuff, or at least figure out how it can interact with non-linear stuff (related to the stuff I already said).

Possible practical applications:
* because the implementation as coroutines, this may be implemented either sequentially or as parallel threads. Parallel reduction (or at least the capacity for parallel reduction which allows broader optimizations) may lead to fast implementation. Unsure of interactions with laziness; generalization of method to non-linear expressions may allow very lazy and efficient implementations?
* hopefully turn this into something practically useful as e.g. an IR or systems programming language (which can also e.g. avoid implicit allocations, have a sane ABI and some reasonable C FFI despite coroutine semantics and weird negative arguments), since that's what motivated this line of reasoning in the first place.
