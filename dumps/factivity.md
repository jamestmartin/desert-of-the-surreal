# Chat dumps on polarity and factivity
These dumps are in chronological order. Later dumps may be more informative.

Each section of the chat dump should be deleted once all of its information
has been incorporated into proper conjectures/articles/whatever.
(That will probably take a long time.)

## Domains
I'd like to elaborate on the connection between the preservation axis and data vs. computation.

Types in Haskell have a denotational semantics related to domain theory (Dana Scott), and their values form a partial order described by Hasse diagrams: http://blog.ezyang.com/2010/12/hussling-haskell-types-into-hasse-diagrams/comment-page-1/

The ⊥ in these hasse diagrams does not represent falsehood, but rather "evidence with 0 confidence". The values at the top of the hasse diagrams represent evidence with *complete* confidence, i.e. what I refer to as values.

A "value" has a completely flat domain whereas a "computation" has a completely non-flat domain, but a type may also have a domain somewhere in-between.
* Positive types, e.g. A ⊗ B and A ⊕ B, have a flat domain; neither A nor B can be bottom.
* Negative types, e.g. A & B and A ⅋ B, have non-flat domain, where either A or B or both can be bottom.

A truth-preserving negation ♯ can be thought of as transforming a type with a flat domain into an entirely unflat domain. Intuitively, ♯A is true if A is "even a little bit true" or "not entirely false", i.e. any component of it is true. It might correspond with this sort of operation:
* ♯(A ⊗ B) ↦ A & B
* ♯(A & B) ↦ A & B
* ♯(A ⊕ B) ↦ A ⅋ B
* ♯(A ⅋ B) ↦ A ⅋ B

Polarly, a false-preserving negation ♭ can be thought of as flattening a type's domain, and is false if A is "not entirely true" or "even a little bit false":
* ♭(A & B) ↦ A ⊗ B
* ♭(A ⊗ B) ↦ A ⊗ B
etc

Finally, a degree-preserving negation preserves the type's domain and polarity. The negation corresponding with the above two is trivial, but you might consider the polarity-preserving duality negation:
* (A & B)⊥ ↦ A⊥ ⊕ B⊥
* (A ⊗ B)⊥ ↦ A⊥ ⅋ B⊥
* (A ⊕ B)⊥ ↦ A⊥ & B⊥
* etc

The intuitionistic negation is a truth-preserving dualizing negation. The intuitionistic double negation is a truth-preserving non-dualizing negation.

So if the domain-⊥ corresponds with zero confidence and a fully-determiend value corresponds with complete confidence, what does it mean to have confidence somewhere in the middle? The quantum interpretation is probability, presumably. I still need to read in to that. So what is it on a classical computer?

Although domains do contain a semilattice, I don't believe this is the algebra we're looking for. We need some algebra where the endpoints are "completely undetermined" and "completely determined". I suspect the answer is in computational complexity:
* we already know ⊥ is morally an infinite loop in Haskell, and fully determined values are obviously constant time.
* intuitionistic type theory cares a great deal about termination for their data types, and productivity for their codata types, when they have codata.
* we already know that some substructural logics correspond with restrictions on computational complexity (e.g. soft linear logic, see nlab)
* presumably iteration would result in an accumulation of error in the quantum sense, and iteration in type theory results in the accumulation of computational complexity, so if this is the correct interpretation, induction will result in reduced confidence, giving the theory an ultrafinitistic flavor
* my preliminary skim of the rules for MTL appears to line up with this interpretation

Then what is the meaning of a *complex* degree? Well, we already have another real interval in type theory, corresponding with the interval type in HoTT, and @ and § seem to correspond with some sort of (dis)equality, so perhaps the complex axis has to do with the interval (and thus also identity) type?

To be clear, I'm not even *conjecturing* any of this really. It's more just my best current hypothesis as I seek to understand what's actually going on. (Though it'd certainly be convenient if my very first hypothesis were true...?)

## Polarity
> I am going to confess that I have virtually no intuition for what additive, multiplicative, and exponential connectives are or how they actually differ. It has been one of the major hinderances in my understanding of systems like linear logic, basic logic, and Lq.

Polarity is the entire reason I'm interested in all of these logics in the first place! We have pretty much exact opposite perspectives, which makes communication really hard, but on the other hand it means our perspectives are complementary, which I think is a good thing.

Polarity is basically the idea that depending on whether you define a connective in terms of its reflection rules or formation rules, you will get a different result, whereas in classical logic you get the same connective. It's the same thing as the verificationist vs pragmatist distinction you gave earlier.

For example, you can define conjunction pragmatically, in terms of its reflection rules: If I know A and B, I must know A, and I must know B. Therefore, to prove A and B, I must prove A and I must prove B. This gets you additive conjunction, or with.

On the other hand, if you define it verificationally, in terms of formation rules: If I have an A and a B, I can prove A and B. Therefore, if I have A and B, I can prove something using A and B. This gets you multiplicative conjunction, or times.

In terms of polarity, the verificationist approach is "positive" and the pragmatist approach is "negative". Note that "additivity vs. multiplicativity" and "positive vs. negative" characterize connectives equally, but not in the same way. each of "conjunction, disjunction, implication" defines two connectives, one of which is positive connective and one which is negative connective, and (of the same two connectives) defines an additive connective and a multiplicative connective, according to duality. specifically:
* with: conjunction, additive and negative
* times: conjunction, multiplicative and positive
* plus: disjunction, additive and positive
* par: disjunction, multiplicative and negative
* implies: implication, negative
* excludes: implication, positive
* negation: self-polar (and self-dual)
the status of implication, exclusion, and negation in terms of additivity and multiplicativity is I believe to some extent one of the goals of our ongoing research regarding the negation lattices.

Like I've mentioned a few times, I have a few separate intuitions for polarity, in no particular order:
* informal domain theory
* factive vs. unfactive evidence
* resources
* data vs. codata
* values vs. computations
* others which I'm not thinking of right now

I would strongly suggest reading the resource interpretation of linear logic for a better idea of additivity/multiplicativity, if you haven't already. It's basically "with additive you get one of them, with multiplicative you get both", which explains it poorly, so reading it is better: https://en.wikipedia.org/wiki/Linear_logic#The_resource_interpretation

The domain theory intuition comes from Haskell programming and laziness vs. strictness. I linked "Hustling Haskell types into Hasse diagrams" earlier, but I don't think it'd make sense to someone with no Haskell experience, short of learning Haskell. There's also the original paper on domain theory by Dana Scott, which was more confusing to me but could possibly be less confusing to you. The intuition there is something like "positive types have flat domains and negative types have non-flat domains":
* http://blog.ezyang.com/2010/12/hussling-haskell-types-into-hasse-diagrams/ (this is a series, not just the one article, btw)
* https://www.researchgate.net/publication/242406560_Outline_of_a_Mathematical_Theory_of_Computation

my conjectured factive evidence interpretation is that in LJ, terms represent factive evidence, and in LDJ, co-terms represent factive evidence, and everything else is (to varying degrees) non-factive. terms are constructed by series of applications of reflection and co-terms by formation. so in LJ, positive terms represent factive evidence and negative terms represent non-factive evidence, and vice versa for LDJ. in LJ, negation is non-factive, so negative co-terms do not represent factive evidence even though arguably they should. presumably in co-LJ, negative co-terms would be factive or something along those lines. I believe in basic logic, all terms are factive, in classical logic, no terms are factive.

the values vs. computations interpretation comes in terms of, for example, in addition to domain theory, the devil of the excluded middle interpretation of computational LEM: http://parametricity.net/b/2012/04/24/the-devil-of-the-excluded-middle/

the negative types (in LJ) represent points where the devil gets to decide which offer to give you. you could also make that sort of interpretation in terms of the game semantics.

Consider how classically, implication can be defined in terms of (multiplicative) disjunction and negation. I believe that implications can be defined *entirely*, if not *exactly*, by negations described by our lattices and (usually?) multiplicative disjunction. Basic logic already *has* two negations in that sense: a basic paracomplete negation used to define implication (or conversely, defined by implication, `→ ⊥`), and a basic paraconsistent negation used to define exclusion (or conversely, defined by exclusion, `1 ←`).

Other systems also have multiple negations and multiple implications. LJ is basically factive, but its negation is non-factive. Its negation is also dualizing, so double negation results in a non-factive, non-dualizing negation. The exponentials in linear logic are also non-dualizing negations, and certain combinations of exponentials with `⊸`, which encodes a dualizing negation, are known to correspond roughly with intuitionistic and classical implication. Agda and Coq are related to LJ, but also have a form of negation (S)Prop and propositional truncation, which describe classical implication in slightly different ways. I posted a question about "double negation-like operators" in PA SE a while back so needless to say I was *extremely* excited about our conjectures.

The potential for a host system like basic logic or Lq to include negations from other systems is very exciting to me. It's part of why I care about lower bounds of logics; I might hope that the lower bound of two logics can potentially contain the negations of the parent logics without trivializing them in a way which lets you speak using implications from the parent logics as a way of transferring non-trivialized results from one logic to another while sharing a common language of connectives.

For the record, based on my (corrected) prediction earlier, I'd expect classical negation to be additive, but that's besides the point.

> Roughly speaking based on a very brain-full reading of it, I'd guess that "flat domain" means linear and Euclidean. Whereas non-flat domains refers to non-linear and either Euclidean or non-Euclidean; I would expect it to correspond to the domain you get when restricted to systems of linear equations vs when restricted to systems of binomial equations or (complex) analytical equations. But I'd need to do a more careful reading to see if my interpretation matches up with the formal reality.

I can't confirm or deny this because I have no idea what any of those words mean. That said, it might be clearer to say that a flat domain does not contain bottom, or alternatively, every term is equally well-defined so the partial order is trivial. The Hasse diagram articles are unfortunately in terms of a dialect of Haskell which does not actually contain any entirely flat domains *or* (strict) multiplicatives, (although as an aside, GHC provides language extensions like BangPatterns and StrictData which make it so), which means the set of examples aren't optimal for demonstrating the distinction, although it does help understand the domain semantics. Here are examples from our actual connectives.

for A & B:
```
    (A, B)
  /       \
(A, ⊥)  (⊥, B)
   \     /
    (⊥, ⊥)
```
for A ⊗ B:
```
(A, B)
```
for A ⊕ B:
```
(Left A)     (Right B)
```
for A ⅋ B:
```
(Left A)  (Right B)
    |         |
(Left ⊥)  (Right ⊥)
```
for ⊤:
```
⊤
|
⊥
```
for 1:
```
1
```
for 0:
```
🦗(nothing here)🦗
```
for ⊥:
```
⊥
```
(note that it's *just* ⊥ the "undefined", there is no actual value of ⊥)

I think it's also interesting to consider the case of the fixed-point combinators μ and ν if you're familiar with those

> A very generalized notion of this is that where classical deductive proofs and refutations vary together exactly, I don't think we should expect that in general [...]
> I think we may have generalizations of the square of oppositions.
> I suspect then that we can have metasystems where a refutation in one of the constituent systems does not necessarily mean that a proof is impossible in one of the constituent proof systems. 

I believe we've been getting at something similar to this w.r.t. the interaction between context-handedness(?) and structural rules. In particular, if you review my original list of conjectures (I did not state it as directly in my revised version), you'll see that conjecture 1.3 (polarity & structurality) predicts more systems than described by the basic cube. In particular I describe (to the best of my ability at the time) the systems "one step down" from LK/BSLR, 1.3.1 describes LJ/BSL, 1.3.2 describes LDJ/BSR, and 1.3.3.3 describes BLR, but I also conjecture additional systems intermediate to BLS and BLR (1.3.3.2; weak NC + weakening (?)) and intermediate to BRS and BLR (1.3.3.1; weak EM + contraction (?)).

The collapse of polarity is related to the interplay between paraconsistency, paracompleteness, and *specific* structural rules, and polarity is related to the relationship between deductive proof and refutation.

## Factivity
non-factive EM is partially true in intuitionistic type theory and thus probably also in LJ. you can prove `∀A. ¬¬(A ∨ ¬A)` which sure looks like `¬(A ∨ ¬A) ⊢ ⊥` which is EM'. This is probably a direct consequence of the identity rule for logics with left contexts and perhaps also explains why negation in LJ is non-factive.

but on the other hand, it's not the non-factive EM we're looking for. ITT proves `∀A. ¬¬(A ∨ ¬A)` but *doesn't* prove `¬¬∀A. A ∨ ¬A`, a principle which is implied by full EM, but which in practice useful far more often. full EM corresponds with undelimited continuations, which are bad; the latter principle corresponds with double-negation shift and delimited continuations, which are known to programmers to be far *less* bad. I'm not sure how the latter EM affects factivity, but I'd like to see how "delimited continuations are less bad" translates as a concrete meta-statement about the logic.

I believe `∀A. A ∨ ¬A` and `¬¬∀A. A ∨ ¬A` are the more useful factive and non-factive EM. many people call `∀A. ¬¬(A ∨ ¬A)` non-factive EM because it gives classical-like properties while simultaneously working in a system which *refutes* actual EM, even though ¬EM and ¬¬EM obviously can't both be true since LJ is explosive. the actual definition of ¬EM is `¬∀A. A ∨ ¬A`, which is indeed provable in HoTT.

but on the other hand, the universal non-factive EM isn't what we're looking for in HoTT either. HoTT's EM axiom is `∀A. ||A ∨ ¬A||`, which is non-factive and resembles the "incorrect" negation of EM. propositional truncation (`||A||`) is proof-irrelevant in a way different from the definitional proof-irrelevance of Prop in a way which I don't understand, but which may be related into the split of proof-relevance into two definitions like we were discussing last night.

> Is there a resource for the framework of this factive evidence interpretation that you're using?

no, the intuition preceded the terminology. it's the same framework as duality and polarity that I keep talking about.

(additive/multiplicative/exponential) multiplicity is a function of (conjunction/disjunction/implication) duality and (positive/negative) polarity: the dual of a connective shares multiplicity and has opposite polarity; the negative of a connective  shares duality and has opposite multiplicity; an exponential's negative and dual are the same connective. so in some sense, multiplicity is a way of talking about the polarity of a connective independently of its duality. but that's not quite right. structural rules break down multiplicity whereas classicality breaks down polarity.

loss of multiplicity (by adding structural rules) without loss of polarity is what gives you the implications. left-handedness causes exclusion to degenerate; right-handedness causes implication to degenerate; structural rules cause par and times to degenerate. this is why LJ has implication but not par, LDJ has exclusion but not times, and CLL has both but no implications.

correspondingly, (non-)factivity (like polarity?) is a function of (context; left/right/both/neither) handedness (like duality?) and (truth/falsity/degree-)preservation (like multiplicity?). a system with opposite handedness exchanges factivity between connectives, and presumably so does a system with opposite preservation, and the factivity of a connective is related to its polarity, so in some sense it lets you talk about polarity in a way independent of those properties. it relates to polarity in that in a left-handed system, positive connectives are factive; in a right-handed system, negatives are factive; with neither, both are factive; with both, neither are factive. dual connectives (with the same multiplicity) have opposite polarity, but on the other hand, the system's "native" negation doesn't reverse factivity; it collapses it, because implication reflects the preservation of its entailment.

so in LJ, negation makes all of the factive connectives non-factive, whereas in LDJ, negation makes all of the non-factive connectives factive.

now here is why I identify the property I call factivity (which I previously called "values/computations" or "data/code") with factivity as described in the LETJ paper (and I think another paper; I don't remember):

in LJ, `¬` flips duality and collapses factivity (among other things), so `¬¬` preserves duality while still collapsing factivity to non-factivity. because entailment is truth-preserving, we have that `A → ¬¬A`, but not `¬¬A → A`. we have `∀A. ¬¬(A ∨ ¬A)` or equivalently `∀A. ¬¬(¬¬A → A)`, which I interpret as "non-factive evidence for non-factive evidence for A suffices as non-factive evidence for A". this isn't sufficient to call it factivity, but I also have this observation: in LJ, the Hasse diagram for negative types allows for undefinedness, where the devil changes his mind. in other words, negative types can contain "proofs" of propositions which *aren't actually true* and which you may be able to refute, which is precisely how LEM works (on one branch you refute the non-factive evidence). on the other hand, (still in LJ, btw) if you have a proof in a positive type you know damn well it's true and you will not be able to refute it (or if you can refute it, you get explosion, anyway). the dual of everything I just said holds in LDJ. in BL, all evidence is factive, and in LK, no evidence is factive.

factive evidence is proof-relevant whereas non-factive evidence is only sort-of weakly proof-relevant (in a way related to eta rules?). much like how a monad is a burrito (i.e. this is a food-based personal intuition and probably not useful), a non-factive A is like "you have money and can walk to the store to buy an apple" whereas a factive A is "I have an apple right here". you can state propositions about an apple you have ("the apple is green") but not an apple you don't have (short of asking for a green apple specifically). this is the sort of weakened equational theory you experience in LK. it may have to do with the two proof-relevance conditions analogously to NC and NC', but I have not thought about it in depth yet. 

there was one other point I wanted to make but I forgot what it was. so fyi if you read that and it feels like a part of the picture is missing, it's because it 100% is. (well, that and the stuff between multiplicativity and factivity which I haven't worked out yet at all.)
