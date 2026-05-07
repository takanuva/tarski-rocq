# Internal Tarski universes in Rocq

![Coq 8.18](https://github.com/takanuva/tarski-rocq/actions/workflows/coq-8.18.yml/badge.svg)
![Coq 8.19.2](https://github.com/takanuva/tarski-rocq/actions/workflows/coq-8.19.2.yml/badge.svg)
![Coq 8.20.1](https://github.com/takanuva/tarski-rocq/actions/workflows/coq-8.20.1.yml/badge.svg)
![Coq 9.0](https://github.com/takanuva/tarski-rocq/actions/workflows/coq-9.0.yml/badge.svg)

There is a problem: Rocq doesn't support [induction-recursion][wikipedia] as
Agda does. This has often been a problem for formalizing dependent type theories
in it, where users tend to compromise and [avoid an universe hierarchy][mctt].
While it is known that small induction-recursion (the case where the codomain of
the recursive function is smaller than the inductive type!) [may be
encoded][hancock] in Rocq, this doesn't allow us to construct the canonical
example of induction-recursion, universes. Or does it?

This project contains an example encoding of _large_ induction-recursion in
Rocq, properly deriving an hierarchy of `nat`-indexed internal Tarski universes
in `Set`, by relying on a feature that in turn Agda doesn't have: an
impredicative `Set`. The trick relies on defining the universe as a small
inductive-recursive type, with the inductive part living in `Type`, _shrinking_
it down using impredicativity to live in `Set`, leaking relevant small
information, and proving that the squashing constructor is an isomorphism.

# Constructing large inductive-recursive types

The eager reader might want to skip this README file and go straight to the
source code; it is commented and should be easy to follow. Our goal is to
define, in Rocq, an inductive type and a recursive function akin to the
following valid Agda definition over a family of sets `A` and `B`:

```agda
postulate
  A: Set
  B: A -> Set

mutual
  data CODE: Set where
    NAT: CODE
    PI: (a: CODE) -> (T a -> CODE) -> CODE
    IDX: CODE
    LFT: (a: A) -> CODE

  T: CODE -> Set
  T NAT = Nat
  T (PI a b) = (x: T a) -> T (b x)
  T IDX = A
  T (LFT a) = B a
```

Or alternatively, imagining some syntax in Rocq for inductive-recursive types,
inspired by the equations plugin:

```coq
Variable A: Set.
Variable B: A -> Set.

Inductive CODE: Set :=
  | NAT: CODE
  | PI (a: CODE) (b: T x -> CODE): CODE
  | IDX: CODE
  | LFT (a: A): CODE

with T: CODE -> Set :=
  T NAT := nat;
  T (PI a b) := forall x: T a, T (b x);
  T IDX := A;
  T (LFT a) := B a.
```

(Please note that while it should be possible to derive the induction principle
for `CODE`, this has not yet been done in this repository, sorry! TODO, I
guess?)

We take the following steps in order to construct this type:

- Define a type of signatures for inductive-recursive definitions ([see
  here][hancock]);
- Assuming the recursive function produces a type `O: Type`, build a functor on $Type/O$ for it;
- Take the least fixpoint of such functor as the impredicative encoding, [as elaborated in here][wadler];
- This will produce the small induction-recursion version of the type and the function, which we call `IND: Type` and `REC: IND -> Set`;
- As we use an impredicative encoding, we create an inductive type `canonical:
  IND -> Type` to represent valid setups;
- We make now a large inductive type in impredicative `Set` (i.e., it contains
  large elements and, if not for impredicativity, could not live in `Set`!), to
  _squash_ the contents of a canonical value of `IND`.

We have, thus, the following piece of code:

```coq
Inductive CODE: Set :=
  | shrink (x: IND) (ok: canonical x).
```

Although this looks quite nice, there's a critical problem: there's no
elimination from `CODE` into large types, thus we can't ever recover the packed
`IND`! Of course, if it would be possible to eliminate from `CODE` into a large
type (such as `Set` or `IND`), and extract the values from the constructor, we
would be able to derive an inconsistency. But the key point: we are allowed to
eliminate still into `Set` and `Prop`, and thus we may leak just enough _small_
information to _reconstruct_ the desired code.

We proceed:

- Make eliminations from `CODE` into `CODE` and `A` (which is alowed) to get the
  arguments, such as recursive elements (i.e., `a` and `b` in `PI a b`);
- Make a subterm relation `subterm: CODE -> CODE -> Prop`, and prove that it is
  well-founded by using the accessibility predicate `Acc` by induction on the
  proof of canonicity of the code (indeed, we're allowed to eliminate from
  `CODE` to produce a mere proposition!);
- As `Acc` is a _subsingleton type_, we are allowed to perform induction on it
  to produce any large type, thus we may define a rudimentary induction
  principle for `CODE`;
- Finally, write a lemma `rebuild` that, by this well-founded induction, uses
  the leaked information to construct the same `IND` that is locked inside a
  `CODE`.

I.e., we prove that the `shrink` constructor, although we can't eliminate from
it to recover the packed `IND`, is in fact an isomorphism.

While shrinking the inductive type has been done for the type of codes directly
in this repository, this should be doable for any inductive-recursive definition
in general.

# Cumulative universe hierarchy

Following [Dybjer][dybjer] and [Palmgren][palmgren], as an exemple of
application for this technique, we define a family of types by induction on some
natural number (similar to the following, in pseudocode):

```coq
Fixpoint A (n: nat): Set :=
  match n with
  | 0 => False
  | S k => CODE (A k) (B k)
  end

with B (n: nat): A n -> Set :=
  match n with
  | 0 => False_rect Set
  | S k => T (A k) (B k)
  end.

Definition U (n: nat): Set :=
  CODE (A n) (B n).
```

(Note that `U n` is definitionally equal to `A (1 + n)`!)

This allows us to make a cumulative hierarchy of nat-indexed universes; in `U
0`, `IDX` is a code for `False`, but for `U (1 + n)`, `IDX` is a code for `U n`.
Furthermore, if `x: U n` if a code, we also have that `LFT x: U (1 + n)`, so,
for example, every universe in this hierarchy contains a code for `False`. Then,
we may even create an even larger universe, still in `Set`, which might be
useful, containing every earlier universe (again, pseudocode):

```coq
Definition Uw: Set :=
  CODE { n: nat & U n } (fun p => T (projT2 p)).
```

Which means that `Uw` contains codes for `U n` for all `n`, as well as codes for
their types. We would expect that, for example, this could be used for defining
a category with families model of some type theory, by having types and terms
live in something akin to `Uw`. We do not define a _superuniverse_ (as described
by Dybjer and Palmgren), that is, an universe closed under universe construction
itself, but this should be a simple extension. In fact, `CODE` could be
abstracted over a family of type constructors, such that, besides $\Pi$-types,
one could also have $\Sigma$-types, $W$-types, and even $M$-types.

# Drawbacks (beware of axioms!)

The main ingredients for the construction were the impredicative `Set` and
subsingleton elimination in `Prop`. However, the code also relies in both
uniqueness of identity proofs and functional extensionality (see [the
code](theories/Tarski.v) for details). If that's a dealbreaker for you, it
should be possible to avoid the need for those axioms by making the
interpretation function produce setoids instead of simple sets, and, in fact,
this is how I intend to do it [in my PhD project][cps]. You might want to check
it out!

# Acknowledgements

I would like to thank my advisor, Dominic Orchard, for encouraging me not to
take "it can't be done, Rocq doesn't support induction-recursion!" as an answer
when I wanted to find a way to encode the internal universe hierarchy.

# License

This code is free software, released under the [BSD 3-clause license](LICENSE).

[wikipedia]: https://en.wikipedia.org/wiki/Induction-recursion
[mctt]: https://dl.acm.org/doi/10.1145/3747511
[hancock]: https://people.cs.nott.ac.uk/psztxa/publ/tlca13-small-ir.pdf
[dybjer]: https://www.cse.chalmers.se/~peterd/papers/Inductive_Recursive.pdf
[palmgren]: https://www2.math.uu.se/~palmgren/universe.pdf
[wadler]: https://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt
[cps]: https://github.com/takanuva/cps
