# The Anatomy of an Object Language
* term syntax
* introduction rules
* elimination rules
* type judgements
* conversion judgements
* evaluation strategies
* models

## Term Syntax
a tree? predicates with input/output arities? directed acyclic graph? graph? arbitrary vertex data?

## Entailment
rules have pre-requisites and conclusions. both are judgements.
proofs, refutations, equalities, and apartnesses may all be interdependent.

contexts are lists? more structured? also terms? judgements are terms? variables are...?

### Proof

### Refutation

### Degree
In the future, entailment may be represented with a non-binary *degree* of entailment.

Futhermore, contexts need not be lists.

## Conversion
### Equality
Equality describes equivalence classes of terms.
All terms in the same equivalence class must be convertible (or reduce to the same normal form) under any model.

Models may choose to introduce equalities between terms which are not required to be equal by the equality judgement,
so long as it does not introduce any equality between separate terms.

"Not equal", or "inequality", describes terms which cannot be proven equal using the equality judgements.
Terms which are not equal are not necessarily apart in all models.

### Apartness
Apartness is an anti-equality relation.
Terms which are apart must not be equal under any model.

Models may choose to leave terms apart which are not required to be apart by the apartness judgement,
so long as it does not leave equal terms apart.

"Not apart" describes terms which cannot be proven apart using the apartness judgements.
Terms which are not apart are not necessarily equal in all models.

### Convertability
In the future, conversion may be represented with a non-binary *degree* of equality and apartness.

Furthermore, conversion need not be separate from entailment.

## Models

## Metalanguage

### Meta-theoretic properties

## Chat Dump
I think I know more-or-less what the subject of abduction, a hypothesis, is, for our purposes. it's a formal theory, e.g. a type theory or formal logic. your metalanguage is a framework for abductively generating type theories, deductively creating models relative to other type theories, and inductively generating type theories by extrapolating properties which hold in your specific model to be properties of an extension of your abductive theory where those properties are rules

presumably we will want to generalize type theories in some sense by continuing to investigate systems like Lq so that we're less constrained in the theories we can talk about in the metalanguage 

seems like the goal of our framework is to create a metalanguage which can be used to describe the rules of any system within our framework 

our conjectures of entailment and embedding non-native entailment express that:
* stronger theories contain models for weaker theories
* our metalanguage should be able to reify the meta-linguistic concept of a theory into the object language

we've established that the strength of the equational theory and the factivity of evidence are properties of paraqualification, so the conjecture about forms of degeneracy consists of some sort of meta-theorems (or at least meta-meta-theorems) about the paraqualification of object languages

another neat thing is that dependent type theories are higher-order, so the metalanguage itself is possibly literally whatever our bottom system is plus some form of higher inductive-inductive types which correspond with object theories.

### Equality & Apartness
I think it's worth distinguishing equality and apartness and proof and refutation

where "equal" means "part of the same equivalence class in every model", "apart" means "not part of the same equivalence class in any model", where "not equal" includes "apart" and "not apart" includes "equal", but there exist terms whose equality and apartness cannot be proven from the rules, and thus there may exist models where those terms may fall in either category

likewise, "provable" means "provable in every model", "refutable" means "refutable in every model", and the principle is the same as for equality and apartness: which category the rest of the statements fall under may depend on the model

thus, "weakly proof relevant" means "has models with non-trivial equality", "genuinely proof relevant" means "has no models with trivial equality", "weakly paraconsistent" means NC or NC' need not hold in a model, "genuinely paraconsistent" means that NC and NC'  fail in all models, etc
