Renan Almeida de Miranda Santos <renan.061@gmail.com>
Well done. 5/5

* [Assignment 1][plfa.Assignment1]

  + Naturals
    - `seven` ok
    - `+-example` ok
    - `*-example` ok
    - `_^_` (recommended) ok
    - `∸-examples` (recommended) ok
    - `Bin` (stretch) good

  + Induction
    - `operators` ok
    - `finite-+-assoc` (stretch) attempted [finite-+-assoc]
    - `+-swap` (recommended) ok
    - `*-distribʳ-+` (recommended) ok
    - `*-assoc` (recommended) ok
    - `*-comm` ok [could be shorter]
    - `0∸n≡n` ok
    - `∸-+-assoc` ok [could be done with three cases]
    - `Bin-laws` (stretch) good [could be simpler]

  + Relations
    - `orderings` ok
    - `≤-antisym-cases` ok
    - `*-mono-≤` (stretch) excellent
    - `<-trans` (recommended) ok
    - `trichotomy` ok [better to use `with` clause]
    - `+-mono-<` excellent
    - `≤-iff-<` (recommended) ok
    - `<-trans-revisited` ok [don't need induction]
    - `o+o≡e` (recommended) ok
    - `Bin-predicates` (stretch) good [Bin-predicates]

[finite+-assoc]

    -- In the beginning, we know nothing.

    -- On the first day we know zero.
    0 : ℕ

    -- On the second day we know one and assoc for zero.
    0 : ℕ   [ assoc 0 m n | m <- [0] ]
    1 : ℕ

    -- On the third day we know two and assoc for one.
    0 : ℕ   [ assoc 0 m n | m <- [0,1], n <- [0,1] ]
    1 : ℕ   [ assoc 1 m n | m <- [0] ]
    2 : ℕ

    -- On the fourth day we know three and assoc for two
    0 : ℕ   [ assoc 0 m n | m <- [0,1,2], n <- [0,1,2] ]
    1 : ℕ   [ assoc 1 m n | m <- [0,1], n <- [0,1] ]
    2 : ℕ   [ assoc 2 m n | m <- [0], n <- [0] ]
    3 : ℕ

[Bin-predicates] I would have done this differently.

    data One : Bin → Set where
      one : ∀ {x : Bin}
          ----------
        → One (x1 x)

