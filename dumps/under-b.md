# U & Under B

> OH. Just got that you're talking about messing with distributivity here. That's what the system U deals with. https://www.researchgate.net/profile/Kiarash-Rahmani/publication/266560337_A_Proof_of_Cut-Elimination_Theorem_for_U_Logic/links/54c3514e0cf256ed5a9117dc/A-Proof-of-Cut-Elimination-Theorem-for-U-Logic.pdf
>
> There's an earlier paper this is referring to but for our purpose this sums that up well enough and elaborates on some important points.
>
> The system U is similar to the system B/B' but the approach to dealing with some of the issues that B/B' deals with is slightly different. B/B' preserves modus ponens and the deduction (meta)rule I believe. U allows modus ponens to fail in general and preserves other qualities instead.
>
> [...]

> In the article I linked, there's definitions of "history" and "linked" for lists in U that sounds like it is related to what you're talking about here. It's under the proof of cut elimination at the top.

**TODO**: This entire discussion still needs to be copied over.

## Proof Search
so the provability predicate is a godel sort of encoding, and by breaking modus ponens you break functional completeness so you can't express the provability predicate?

so I recognize that you have some sort of notion of computation in terms of internalized cuts or something which is on my (large) todo list of things to understand, but it's not clear to me how it relates to the type-theoretic view. my best guess so far is that it corresponds with logic programming languages and solving unifications as opposed to functional programming languages, or perhaps to some sort of internalized eval-like function.

from a functional point of view, any of the logics contain precisely zero interesting computation until you start adding inductive types. a language based on constraint solving might be computationally more interesting than that; I'm not sure.

> [the above is a quote from a much older conversion which Paraconsista directs me to]

a truth predicate would reflect model-specific reasoning whereas a provability predicate would not?

without modus ponens proof search becomes decidable? is that it?

because the liar's paradox would present an infinite loop for proof search, effectively.

part of the hard part is knowing how many times to apply functions in the context? and sans-functions, maybe you can tell whether your proof is structurally larger than the desired conclusion?

> [Paraconsista links to more old stuff]

so the provability predicate is a godel sort of encoding, and by breaking modus ponens you break functional completeness so you can't express the provability predicate?

> That sounds about right.
>
> Breaking modus ponens critically breaks a metarule that is common to classical-like systems called the Deduction Rule(s).

> For classical systems and any system which meets the minimum conditions for Gödel's proof, proof and truth will be separable concepts. There will be things expressible in the system and by the rules of the system which are neither provable nor refutable in that system.
>
> In some philosophies and frameworks of logic, this is an unacceptable condition. 
> * What is provable is true; what is not provable is not true or we must pass over in silence that which can not be proven. 
> * What is false is refutable; what is not refutable is not false or we must pass over in silence that which can not be refuted.
>
> If you want your proofs and tautologies to be one to one and your system to have 1st order or higher expressive power then modus ponens can't stand. 

> For classical first order theories, if the theory is decidable then it is axiomatizable; if the theory is decidable and complete then it is decidable.
>
> If the theory is not decidable then it is incomplete and axiomatizable, incomplete and non-axiomatizable, or complete and non-axiomatizable.

**TODO**: A lot more stuff needs to be copied here.
