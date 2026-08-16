outline prompt for a 25min talk. Claude, can you generate a slides for
me in the template qpl26slides/talk.lagda.tex?

(note: when generating circuit using Cir2Tikz, pay attention to: the
circuit order is the reverse of the multiplication order (i.e., the
Word order _•_))

# title "A complete and natural rule set for multi-qudit Clifford
  circuits in all odd prime dimensions"

  - Authors are the same as in paper qudit-quantum-july-9.pdf

  - emphasize that all the codes in this slides are checked by Agda.

  - emphasize that this slides is written by me and Claude. I wrote a
    200 loc or so outline prompt (this file) for Claude.

## Introduction

### From qubit Clifford operators to qudit Clifford operators

    - compare the defs for H, S, and CZ gate in qubit and qudit case.
    - show extended gate defs: X, Z, Ex (Swap), CX, XC

### Main result1: A presentation in terms of generators and relations
    for qudit Clifford operators, as shown in
    Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Presentation
    (copying the code to the slides)
    
    - emphasize g is a fixed multiplicative generator of Zp*, i.e. the
      presentation is parameterized by g.

#### Show the relations in code and the relations in circuit mode
     using the tool Cir2Tikz.

#### Explaining _IsPresentationOf_, i.e. there is an isomorphism:

		    ⟦_⟧
       Cir/_===_  ------>  group of Clifford operators


### Main result2: A unique normal form for qudit Symplectic (Clifford
    modulo Pauli) operators, as shown in
    Examples.Groups.Symplectic.Normalization.Boxes.

#### Show the NF in circuit form.

#### Show the code for NF and ML; explaining the double induction
     structure --- ML is inductively defined and so is NF.

### Main feature: Agda checked.


## Method

### Divid and conquer: factor the group, find the presentations for its
    "factors" and then compose the factor presentations up.

    - show the two extensions: 1) semidirect product of projective
      Pauli and Symplectic group; 2) central extension of the
      projective Clifford and Scalars.

    - Symplectic operators are the "proper" Clifford operators, such
      factorization appears only reduce the complexity cosemetically,
      but actually no, such factorization helps a lot, especially in
      circuit rewriting.

    - emphasize that the privious work on qubit Clifford and qutrit
      Clifford did not use the "Divid and conquer" method and their
      derivations contain "messy" Pauli part.

### Rewrites to the unique normal form: find a presentation for the
    main factor --- the Symplectic operators.

#### find a unique normal form for each symplectic operator

     - Show the code for NF and ML again and their circuit; also show
       NF 4 in circuit as an example; show all ML 3 in circuit (trace
       down to basic boxes --- A, B , D , E).

     - Explaining the idea of normal form and uniqueness of normal
     form through the example of Sn.

     - draw all circuit for S_3

     - draw all circuit for C_2

     - point out that for each element f in S_3, we can find c in C_2
       such that f^{-1} * c in S_2, i.e. f^{-1} * c fixes the bottom
       wire, by induction let g be the normal form of (f^{-1} * c) ^
       {-1}, then f has normal form c * g

     - if c in each C_n is unique them c * g is unique

     - c is an elemen that take f^{-1}(0) to 0, hence uinque

     - We are using the action of Sn on {0,...,n-1}. we can also let
       Sn acts on Vector Bit n; now each wire represents a bit, then c
       is the unique elment such that f^{-1} * c fixes the Z_2 linear
       subspace Bit represented by the bottom wire

     - We can also let Sn acts on the group of n-qudit projective
       Pauli operators --- Vec Pauli1 n. Vec Pauli1 n enjoys more
       structure beside it is a 2n dim Z_p linear space: it is a
       symplectic vector space. now f^{-1} * c fixes the symplectic
       subspace Pauli1 represented by the bottom wire.

     - We can then add more gates H, S, CZ in to get all Symplectic
       circuit. By enlarging C_n, we can show for all f in the
       symplecic group Sp(2n, Z_p) (i.e., the linear maps between
       Symplectic spaces that preserve symplectic form), f^{-1} * c
       fixes the subspace.

     - Show the circuit for NF 4 and ML 3 again and point out the
       structure; point out such framework works for any circuits,
       i.e. any Nat indexed groups with such "layered" structure.

     - Point out such normal form is widedly used in group theory: If
       you have a tower of subgroups G_0 < G_1 < ... < G_n, and if you
       know the coset representatives of C_k = G_k/G_{k-1}, then you
       know the norma forms for elements of Gn is {PI c_i | c_i in
       C_i}, i.e., a mix-radix encoding of the group G_n. Point out
       Circuit natrually has such tower of sugroups i.e., Cir 0 < Cir
       1 < ... < Cir n

     - The diffculty is to construct systematically the coset
       representatives C_k. This is done in a similar way as in
       qubit-clifford paper and qutrit-clifford paper.

#### Show the code for Uniquness proof unique-nf in
     Symplectic.Normalization.Uniqueness
     
     - draw a tikz figure :
     
		    ⟦_⟧
       Cir/_===_  ------>  Sp(2n, Zp)
       
        /|\   |
  inv-nf |    | nf
	 |   \|/
	  
	   NF
	   
     - unique-nf says (⟦_⟧ ∘ inf-nf) is injective


#### rewrite every circuit to nomral form and collect the rewrite
     rules used (e.g. 67 rules in our case)
     
     - still using Sn, show the four case of pushing a generator
       through a coset C_k in circuits.

     - Show a few of the box relations in circuit.

#### by inspecting the rewrite rules, by using intuition, find a
     bounch of primitive relations (bi-directional rewrite rules) such
     that repeated use of the primitive relations implies all the
     rewriting rules.

     - in this step, one can choose to use different sets of primitive
       relations depending on one's preference: show the relations in
       Examples.Groups.Symplectic.Simplified.Syntactics in circuit
       using Cir2Tikz tool.

     - include Figure 8 page of qubit-clifford/clifford.pdf

     - compare two relation sets: identical 3-qudit relations; almost
       identical 2-qudit relations; more complicated 1-qudit
       relations.

     - Show an example in detail and in cicuit of how to derving M x *
       My = M (x * y).
     
     - show the code presentation in
       Examples.Groups.Symplectic.Simplified.Presentation

### Composition

#### show again the two extensions: 1) semidirect product; 2) central
      extension.

#### Show the Pauli relations code in
     Examples.Groups.ProjectivePauli.Presentation-Alt

#### Show how the semi-direct product relations is constructed

     - explaining how to construct a presentation for the direct
       product of two groups whose presentations are known. (n , h) *
       (n' , h') = (n*n', h*h')
       
     - further explaining how to construct a presentation for the
       semi-direct product of two groups whose presentations are
       known. (n , h) * (n' , h') = (n * h * n' h^{-1} , h*h') =
       (n*n'' , h * h').

     - explaining the semi-direct product structure implies the
       projection is a group homomorphism, that is all symplectic
       operators embeds nicely into the Clifford operators. Show the
       lifting defintion in code. Point out the symplectic relations
       can by lifted too.

#### Plumbing: presentation simplification

     - explain equivalent presentations, i.e., there is a group
       isomorphism between two presented groups.
     
     - generator reduction and relation reduction comparing two
       presentations in ProjectiveClifford/Qupit: SemiDirect and
       Siimplified-V1. compare there generators and relations

     - Further, how to get scalars back. Show the relations in
       ProjectiveClifford/Qupit/Simplified-V1/Syntactics.agda in
       circuit with corrected scalars, together with omega ^ p = 1.

## Conclusion

   - Main result1: A presentation in terms of generators and relations
     for qudit Clifford operators and Symplectic operators.

   - Main result2: A unique normal form for qudit Clifford operators
     and Symplectic operators.

   - Both are checked by Agda, except for the proof that the
     projective Clifford operators is a semi-direct product of the
     Symplectic operators and projective Pauli operators, and the
     proof that Clifford operators is a central extension of
     projective Clifford operators by scalars.
      