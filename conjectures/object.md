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
