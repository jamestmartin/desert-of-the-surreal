# Implementation
The programming language shall be named Darius, probably.

* destination object language identified with metalanguage
  * "quote" to convert metalanguage to object language; "eval" to convert back
  * implement "compilers" for object languages (& inductive definitions of types, etc) by producing models in destination language
  * should have inconsistent(/unsound?) variant to serve similar purpose to System F in GHC
    (i.e. reduced target language which allow proofs which can't be statically verified)
  * needs to be able to support complete generality of desired object languages including intervals, complex degree, classicality, parallel non-strictness, and linearity
    * needs to preserve necessary properties of object languages during reduction
	* clasicality via non-determinism, parallel non-strictness via threads
* open/partial evaluator, specializer. used for dependent typechecking and optimization.
  * necessarily graph-based; must be possible to reify into term language; change term language if necessary
  * ideally completely lazy (or some variant of optimal?)
  * normalization function for interaction nets for NbE? not sure what the alternative is
  * support multithreaded parallel reduction
* partially evaluated graph closed up to IO compiled into machine code
  * graph "pinned" at main function and any declared exports
  * this is the "extraction" part. if possible it'd be even better if it can work on open graphs so we can JIT functions during dependent typechecking.
  * possibly verified in Coq using SAIL or something; alternatively, expose ISAs as object languages
  * preferably, but not necessarily, preserve complete laziness semantics
* (hopefully minimalist) runtime interprets IO object language
  * should be inlined and "link-time" optimized, possibly as part of partial evaluation, as much as possible
  * based on parallel asynchronous IO queues (e.g. io_uring, epoll, vulkan, wayland)
    * be able to fallback to synchronous IO, with or without threading, based on platform
	* includes stuff like C ABI calls/receives in general; C ABI preserved by pausing caller thread until reply ready
  * should be possible to statically determine (and avoid via restriction of features) use of:
    * garbage collection / non-termination (or non-liveness) / threads required to preserve semantics
    * dynamic allocation / unbounded computation (even with termination) / coroutines required to preserve semantics
    * information effects / polynomial computation / stacks? required to preserve semantics

a positive inert subnet is an interaction net composed solely of constructors and a negative inert subnet is an interaction net composed solely of eliminators. they are "inert" because they cannot be reduced further, and because composing them with another subnet of the same polarity gives another inert subnet. every inert subnet can be flipped entirely backwards to give an inert subnet of the opposite polarity.

want to be able to control some stuff statically, without memo table or oracle:
* can I use polarity in an interaction net to minimize use of oracle?
* information preserving/producing/consuming/manipulating:
  * determines how constructors and eliminators can be used for additives
  * describes isomorphisms and paths in systems like HoTT; equivalences, injections, surjections, arbitrary functions
  * quantum/heat effects
* constant/polynomial/unbounded-finite/unrestricted time/space:
  * effectively a measurement of factivity? ultrafinitist flavor.
  * unrestricted vs. unbounded deals with partiality, but need that be treated separately?
  * to some extent controlled by restricted exponentials as in soft linear logic?
  * related to sharing and extent of non-determinism?
* linear/relevant/affine/structural, owned vs. borrowed vs. shared? unique?
  * relevant things should always be computed; affine things should ???; non-affine things may need to be duplicated with sharing
  * threading and non-determinism are probably relevant
  
it has a lot to do with non-determinism and non-determinism of inverses or duals.
