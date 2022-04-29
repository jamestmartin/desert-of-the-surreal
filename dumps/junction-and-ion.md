# Junction & Ion
This dump is in chronological order. The parts near the bottom are more recent and more meaningful,
but also may depend on previous context.

## Factoring partial equalities
I have some thoughts which don't quite form a full picture yet.

we know we can factor `A ⊕ A` into `2 ⊗ A`. but when can we perform factorings like that in general with `A ⊕ B`? what we have so far is that `A ≡ B → (A ⊕ B ≡ 2 ⊗ A) & (A ⊕ B ≡ 2 ⊗ B)`. you can factor that into `(eq : A ≡ B) → A ⊕ B ≡ 2 ⊗ ((i : 𝕀) → eq i)`. but consider if you only had `A = C ⊗ D` and `B = C ⊗ E`. you ought to be able to factor out `2 ⊗ C ⊗ ??` but the scheme is not general enough because `C ⊗ D` and `C ⊗ E` are only partially equal, not entirely equal. how can we represent "partial equality" in a way which lets us factor out the `C`?

in fact, something I've known for a long time is that `A ≡ B` *is a form of the eliminator for `⊕`*. In particular, you keep the constructors `inj₁ : A → A ⊕ 0` `inj₂ : A → 0 ⊗ A` and then split the eliminator into a neutral `bimap : (A → B) → (C → D) → A ⊕ B → C ⊕ D` and an eliminator `solved : A ⊕ A → A`. you can take a similar approach to any of the connectives.

so what if we have a type which we can factor out `A ⋆ B` into `C ⊗ ??` without including the `2` at all? basically `A ⊕ B` where we don't care which side we're on, and our sole goal is to unify `A` and `B`? this is the information-conserving equivalent to `⊕`. `bimap` lets us distinguish the sides because we can do e.g. `bimap inj₁ inj₂` which lets us recover the `2`. so instead we have to split `bimap` into `biequiv` where the functions must be information-conserving permutations (equivalences/equalities) and `factor⋆⊗ : (A ⊗ C) ⋆ (B ⊗ C) → (A ⋆ B) ⊗ C` and `factor⋆⊕ : (A ⊕ C) ⋆ (B ⊕ C) → (A ⋆ B) ⊕ C` and so forth, and distributivity laws. in fact, with univalence, `biequiv` is `factor` over equalities, I believe.

`A ⋆ B` is very strange. it's a black box which only lets you extract the portions of the types which you can prove are equal. it's also a supertype of `A ⊕ B` but it's not the same either, because it forgets the bit. it's seems sort-of dual to *some* form of equality in that to fully consume an `A ⋆ B` you sort-of additively prove that `A ≡ B`. but it's also not quite dual to equivalence because you also have to consume the values you factored out, and it's additive, so there's no NC you can insert to produce a function.

on the other hand it also resembles `⅋`. with `⅋` you know that you'll be forced to evaluate both sides, so you can *always* factor out the common subexpressions (compared with `⊕`).

it looks to me like a single fiber of a cubical equality, or something like that. for `PathP eq x y` there exists some proof `eq : A ≡ B` but you don't know what it is, and you have a "value" which is sort-of both `x` and `y`.

more broadly you have `Σ A B` factoring into `A ⊗ B` up to some partial equality. `Σ` can be thought of in terms of "how much do we need to inspect `A` to inspect how much of `B`?" If `B` is constant over `A` (i.e. equal to some constant type for all `A`) then we need not inspect `A` at all. more examples: in `B x = (D, E x)`, then we need not inspect the `A` to inspect the `D` part of `B`. some portion of `B` is constant across all inputs, for some sort of partial equality. what about `Σ 2 λ x → if x then B ⊗ C else C ⊗ B`? `B ⊗ C` is equivalent to `C ⊗ B`, but you can only inspect it without inspecting `A` first if they are equal via univalence.

next consider `Π A B`. how much of `A` do we have to provide to inspect the output `B`? in the case of e.g.
```
f (inj₁ x) = inj₁ x
f (inj₂ y) = inj₁ y
```
we need not inspect the input at all to know that we'll get `inj₁`. but how do we *know* that we're able to inspect both sides? an optimal evaluator needs to use an oracle. there is a partial equality in the output of the function. I notice that an equivalence has no partial equalities in the output whatsoever. what about something like
```
f (inj₁ (inj₁ x)) = inj₁ ...
f (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
f (inj₂ (inj₁ x)) = inj₁ ...
f (inj₂ (inj₂ x)) = inj₁ ...
```
? there is a partial equality in the inner portion; inner inj₁s always map to outer inj₁s in the output...

another thought. we know that we can *always* factor out partial equalities in the outputs with `⅋` because we know both sides will always be evaluated. we can *never* factor out partial equalities with `⊕` because that would require evaluating both sides when we know that we can only use one side. on the other hand, if it were embedded in a function, we could potentially end up calling both sides, depending on the input, and optimally we need to share. when can we treat `⊗` like `⅋`, in this sense? or `&` like `⊗`?

the vague intuition generating these ideas is that....
﻿
thinking in terms of interaction nets, multiplicatives split into "wires". structural rules duplicate, drop, and exchange wires. additive connectives are defined in terms of multiplicatives and structural rules (duplicate the context shared across both sides, and then drop the path not taken).
﻿
optimal evaluators require an oracle/bookkeeping to know what parts of the net will need to be evaluated now and which ought to be deferred until later. but we know that with multiplicative connectives, we *always* can evaluate both sides now, and with additive connectives, we will *never* evaluate both sides (and the duplicates/drops are moot because the duplicate will always be met with a drop of the unused side). so by translating linear terms into interaction nets, we're *losing* information which we *really want* to preserve for efficiency.
﻿
furthermore, interaction nets do a really poor job of handling information conservation. multiplicative wire-juggling doesn't lose information without structural rules. likewise, additives shouldn't lose information either *if they are permutations*. but without structural rules, multiplicative wire-juggling *is also just permutations*. so why can't we define the additives in terms of wire juggling too?

that brings us to kwak's idea of rules with multiple conclusions. why not define additives as an axis of wires *orthogonal* to the multiplicative axis? what we previously split into multiplicative wires using structural rules we now split into multiple orthogonal *planes*. with multiplicatives, the constructor takes two wires and creates one wire and the eliminator takes one wire and creates two wires. thus, the additive constructor takes two planes and partially merges them into one plane, and vice versa. *where we previously had `inj₁` and `inj₂`, we now have `inj`, which is information-conserving because it conserves the number of planes*. our additive rule of contraction allows us to duplicate a plane, allowing us to recover the injections depending on which plane we merge into. our additive rule of weakening lets us merge planes without turning them into additives, allowing us to forget information.
﻿
thus, *conservation of information is just structural rules for additive connectives*.
﻿
then critically, *we want to be able to share parts of the planes*. I guess you might say you *entangle* them? instead of orthogonal planes and wires you have a sort-of flat structure with blobs sticking out or whatever. the shared parts of the planes are precisely the parts which we *always* want to evaluate, optimally. our "partial equality" describes some sort of degree of entanglement between planes.

(that is, presuming the use of the word "entanglement" is correct here. though the concept holds regardless of whether that particular application of the word is correct.)

combine with what I've been saying with the information complexity-based interpretation of the structure of propositions somehow.... seems very relevant, still not sure how to integrate it, though.

also, does this make the additives the same as the multiplicatives "rotated 90 degrees" whereas duals are "rotated 180 degrees" with partial equalities as a connective relating them or something?

(actually probably not, because duals are rotation against a different axis or something like that I think)

okay, here's a weird idea: what if factoring ("partial equality") and `⋆` are duals, and the "correct" additives corresponding with times (multiplicative factoring) and par, whereas `;` is the multiplicative conjunction corresponding with plus and with?

because plus encodes information in the additive exchange rule. swapping left and right corresponds with flipping a bit, but the specific idea behind `⋆` is to factor out that bit. so additive exchange gives you something different with plus but the same thing with `⋆`. on the other hand, times and par are sequentially unordered so exchange doesn't matter, whereas `;` has a strict ordering. likewise, with `;` you get the information about which side happened first. or maybe you could have a sequence-relative connective relating to racing threads or something in which case you'd *really* have a bit of information, but that sounds like a bad idea.

the difference between plus and with is basically *who* gets to decide the value of the bit, but with `⋆` there *is* no bit, so in some sense it's a *purely additive* connective with no conjunctive or disjunctive value, right?
﻿
likewise, with times and par, the only difference is who gets to decide the order in which the sides happen. whereas with `;`, the order is fixed, so neither side gets to decide, so it once again lies at the unification of conjunction and disjunction, making it *purely multiplicative*.

anyway, perhaps in the same way removing structural rules gets you polarity, removing exchange rules gets you neither-conjunctive-nor-disjunctive connectives? does Lnq have exchange?

> Lq and Lnq don't even have exchange; this makes them part of the category or class of non-commutatitve logics or order logics or non-abelian systems.
>
> Getting rid of exchange gives us the ability to express entanglement as an operator in L2q and beyond. 
>
> the multiplicatives of Lnq for n>1 are non-idempotent as a result of the elimination of exchange and the general non-commutative behaviors of the additives in Lq.
>
> Conjunction and disjunction in Lq are non-commutative due to sensitivity to the degrees associated with them, so you can't just exchange the arguments on the operator; you have to exchange the degrees as well otherwise you're doing something weird in an inverse sense to the meaning of the connective.
>
> L2q, Zizzi only considers maximally entangled systems, so the additives are treated as if they're in that case which means the precise condition where they become commutative again.

and once again, the degrees are the information-complexity of each side, presumably

> Basically, yeah. Given that Lq represents the logic of a quantum of information, the degrees on the connective represent symmetries or asymmetries inside the space of the quantum of information. When they're commutative, the system is symmetric. When they're non-commutative, the system is generally asymmetric (anti-symmetric?). I think

> Helps to know that entanglement means non-separable. Related to the concept of irreducibility. A system which is necessarily described by quantum entanglement can not be reduced except by cuts to its apparent constituent elements. It is not decomposable into real values if we think of it in terms of polynomial decomposition.
>
> There's this thing with imaginary numbers and complex valued systems where negations end up being related to rotations which are related to multiplications by imaginary components. This is a significant aspect of quaternions and octonions.

## *ion
dumb point but `⋆` is just a union type and its dual is an intersection type

well, actually, I guess it's not because a union type would imply a syntactic union of both sides, but this is a semantic union because you can still apply equalities or equivalences to either side

alternatively I guess univalence is the axiom which unifies syntactic and semantic unions?

univalence has the interesting property that it lets you retroactively modify the code used to construct the union before the information about which side was chosen was lost

which is sort-of time travel-y and intuitively desirable, but on the other hand it'd imply that univalent unions are lazy and non-factive and UIP unions are strict and factive

so like how EM makes positive types non-factive and NC makes negative types non-factive, univalence makes union types non-factive

consuming a union lets you choose C arbitrarily, so by duality, consuming an intersection in either way ought to somehow "forget" the equality used by the union which makes it kinda degenerate and act more similarly to & because you're effectively stuck with whatever decision you've made. but an advantage of union/intersection types ought to be that you can change your mind arbitrarily and use bits and pieces of either half however you want.

but presumably you could have a "dependent intersection type" where the union's choice of C is restricted, so consuming some piece of A gives you the intersection of the *rest* of A **or** the (dependent) union of all possible choices of C.

now non-dependent junction naturally bifurcates into "two" connectives which are identical except for that the arguments are flipped. but the dependent junction is actually an argument of *four* connectives, representing both a positive and negative obligation in both the input and output., where both output obligations may depend on both input obligations. the dependent connectives are inherently ordered to a degree expressed by a partial equality (inspecting what parts of the input let you inspect what parts of the output based on the equality over the dependent type family), but splitting the dependent connectives in two makes you enforce an order between the positive and negative obligations, which clearly isn't right.

basically, you want to factor junction out into "join points", where *both* the positive and negative obligations are required to get the next bit of information you want, so you want some junctions to be combined so avoid accidentally enforcing ordering constraints, but you also want to be able to provide the *minimum* amount of information possible to proceed, so you want to factor it into as many sequential junctions as possible *up to* the join points.

or I suppose more accurately, you *can't* factor dependent junction *because* it enforces ordering constraints, but junction also combines both times and par in that it enforces a strict order. on the other hand, times lets "you" choose an order and par lets "them" choose an order, so what you really do is factor *times* into junction. so you also ought to have dependent products and dependent sums which *do* let you choose order, and the "factoring" I described is the act of isolating the order-wise degrees of freedom in products and sums *into* sequential junctions.

and the act of "factoring" is the act of *fixing evaluation order in a way which is optimal according to the order in which you use the information*. so for a fully factored system without exchange, optimal evaluation is presumably "free", by definition?

also, this makes me realize that dependent products aren't a generalization of "times" but rather a generalization of "implies" and likewise dependent sums for "excludes", which I guess tells us what happens to exclusion in intuitionistic systems.

I know I just said a lot, but I think this is the probably the difference between the families of **B and B'**: B has dependent types, B' does not.

anyway, likewise, "dependent \*ion" probably doesn't directly generalize union and intersection (which are entanglement?), but rather two entailment-like connectives which are probably the *actual* (dis?)equalities that we are looking for

also, a further conjecture would be that the analogous property to the multiplicative implication bifurcating the system into B and B' would be the additive implication/equality bifurcating the system into univalence or UIP

(by the way, the source of the naming for "junction" is that it is the intersection of (con/dis)junction and likewise "ion" is the intersection of (un/intersect)ion.)
