\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)

--------------------------------------------------------------------------------
--
-- NATURALS
-- 
--------------------------------------------------------------------------------

-- exercise [seven]
-- write out 7 in longhand

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))
_ : seven ≡ 7
_ = refl

--------------------------------------------------------------------------------

-- exercise [+-example]
-- compute 3 + 4, writing out your reasoning as a chain of equations

_ : 3 + 4 ≡ 7
_ = begin
  3 + 4                                         ≡⟨⟩
  suc 2 + 4                                     ≡⟨⟩
  suc (2 + 4)                                   ≡⟨⟩
  suc (suc 1 + 4)                               ≡⟨⟩
  suc (suc (1 + 4))                             ≡⟨⟩
  suc (suc (suc 0 + 4))                         ≡⟨⟩
  suc (suc (suc (0 + 4)))                       ≡⟨⟩
  suc (suc (suc 4))                             ≡⟨⟩
  suc (suc (suc (suc (suc (suc (suc zero))))))  ≡⟨⟩
  7                                             ∎

--------------------------------------------------------------------------------

-- exercise [*-example]
-- compute 3 * 4, writing out your reasoning as a chain of equations

_ : 3 * 4 ≡ 12
_ = begin
  3 * 4                   ≡⟨⟩
  suc 2 * 4               ≡⟨⟩
  4 + (2 * 4)             ≡⟨⟩
  4 + (suc 1 * 4)         ≡⟨⟩
  4 + (4 + (1 * 4))       ≡⟨⟩
  4 + (4 + (suc 0 * 4))   ≡⟨⟩
  4 + (4 + (4 + (0 * 4))) ≡⟨⟩
  4 + (4 + (4 + 0))       ≡⟨⟩
  12                      ∎

--------------------------------------------------------------------------------

-- exercise [_^_] (recommended)

-- define exponentiation

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1 
m ^ (suc n) = m * (m ^ n)

-- check that 3 ^ 4 is 81

_ : 3 ^ 4 ≡ 81
_ = begin
  3 ^ 4                         ≡⟨⟩
  3 ^ (suc 3)                   ≡⟨⟩
  3 * (3 ^ 3)                   ≡⟨⟩
  3 * (3 ^ (suc 2))             ≡⟨⟩
  3 * (3 * (3 ^ 2))             ≡⟨⟩
  3 * (3 * (3 ^ suc 1))         ≡⟨⟩
  3 * (3 * (3 * (3 ^ 1)))       ≡⟨⟩
  3 * (3 * (3 * (3 ^ suc 0)))   ≡⟨⟩
  3 * (3 * (3 * (3 * (3 ^ 0)))) ≡⟨⟩
  3 * (3 * (3 * (3 * 1)))       ≡⟨⟩
  81                            ∎

--------------------------------------------------------------------------------

-- exercise [∸-examples] (recommended)
-- compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations

-- _∸_ : ℕ → ℕ → ℕ
-- m ∸ zero = m
-- zero ∸ (suc n) = zero
-- (suc m) ∸ (suc n) = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ = begin
  5 ∸ 3         ≡⟨⟩
  suc 4 ∸ suc 2 ≡⟨⟩
  4 ∸ 2         ≡⟨⟩
  suc 3 ∸ suc 1 ≡⟨⟩
  3 ∸ 1         ≡⟨⟩
  suc 2 ∸ suc 0 ≡⟨⟩
  2 ∸ 0         ≡⟨⟩
  2             ∎

_ : 3 ∸ 5 ≡ 0
_ = begin
  3 ∸ 5         ≡⟨⟩
  suc 2 ∸ suc 4 ≡⟨⟩
  2 ∸ 4         ≡⟨⟩
  suc 1 ∸ suc 3 ≡⟨⟩
  1 ∸ 3         ≡⟨⟩
  suc 0 ∸ suc 2 ≡⟨⟩
  0 ∸ 2         ≡⟨⟩
  0 ∸ suc 1     ≡⟨⟩
  0             ∎

--------------------------------------------------------------------------------

-- exercise [Bin] (stretch)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

-- inc 0 ≡ 1
_ : inc (nil) ≡ x1 nil
_ = refl
_ : inc (x0 nil) ≡ x1 nil
_ = refl

-- inc 1 ≡ 2
_ : inc (x1 nil) ≡ x0 x1 nil
_ = refl

-- inc 2 ≡ 3
_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ = refl

-- inc 3 ≡ 4
_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ = refl

-- inc 4 ≡ 5
_ : inc (x0 x0 x1 nil) ≡ x1 x0 x1 nil
_ = refl

-- natural to binary
to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

-- to 0
_ : to 0 ≡ x0 nil
_ = refl

-- to 1
_ : to 1 ≡ x1 nil
_ = refl

-- to 2
_ : to 2 ≡ x0 x1 nil
_ = refl

-- to 3
_ : to 3 ≡ x1 x1 nil
_ = refl

-- to 4
_ : to 4 ≡ x0 x0 x1 nil
_ = refl

-- natural from binary
from : Bin → ℕ
from nil = 0
from (x0 b) = from b + from b
from (x1 b) = suc (from b + from b)

-- from 0
_ : from nil ≡ 0 
_ = refl
_ : from (x0 nil) ≡ 0
_ = refl

-- from 1
_ : from (x1 nil) ≡ 1 
_ = refl

-- from 2
_ : from (x0 x1 nil) ≡ 2 
_ = refl

-- from 3
_ : from (x1 x1 nil) ≡ 3 
_ = refl

-- from 4
_ : from (x0 x0 x1 nil) ≡ 4 
_ = refl

--------------------------------------------------------------------------------
--
-- INDUCTION
-- 
--------------------------------------------------------------------------------

-- exercise [operators]

-- give an example of a pair of operators that have an identity and are
-- associative, commutative, and distribute over one another

-- addition (+) and multiplication (*)
--   identity (0 and 1):
--     0 + n ≡ n ≡ n + 0
--     1 * n ≡ n ≡ n * 1
--   associativity:
--     (a + b) + c ≡ a + (b + c)
--     (a * b) * c ≡ a * (b * c)
--   commutativity:
--     a + b ≡ b + a
--     a * b ≡ b * a
--   distributivity (* distributes over +):
--     (a + b) * c ≡ (a * c) + (b * c) ≡ c * (a + b)

-- give an example of an operator that has an identity and is associative but
-- is not commutative

-- concatenation (.)
--   identity (empty string):
--     a . "" ≡ a ≡ "" . a
--   associativity:
--     (a . b) . c ≡ a . (b . c)
--   not commutative:
--     a . b ≢ b . a

--------------------------------------------------------------------------------

-- exercise [finite-+-assoc] (stretch)

{-

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

-}

--------------------------------------------------------------------------------

-- exercise [+-swap] (recommended)

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

--------------------------------------------------------------------------------

-- exercise [*-distrib-+] (recommended)

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p |  sym (+-assoc p (m * p) (n * p)) = refl

--------------------------------------------------------------------------------

-- exercise [*-assoc] (recommended)

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

--------------------------------------------------------------------------------

-- exercise [*-comm]

-- lema 1
*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc m) rewrite *-zeroʳ m = refl

-- lema 2
*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n rewrite *-zeroʳ n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) n rewrite *-comm m n | sym (*-suc n m) = refl

--------------------------------------------------------------------------------

-- exercise [0∸n≡0]

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc _) = refl

-- induction was not required

--------------------------------------------------------------------------------

-- exercise [∸-+-assoc]

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
∸-+-assoc (suc m) zero p rewrite 0∸n≡0 (suc m) = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

--------------------------------------------------------------------------------

-- exercise [Bin-laws] (stretch)

-- from (inc x) ≡ suc (from x)
from-inc≡suc-from : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
from-inc≡suc-from nil = refl
from-inc≡suc-from (x0 x) = refl
from-inc≡suc-from (x1 x) rewrite
  from-inc≡suc-from x | +-suc (from x) (from x) = refl

-- to (from x) ≡ x
-- false
-- when x equals nil:
--   to (from nil) ≡
--   to 0 ≡
--   x0 nil
-- nil ≠ x0 nil

-- from (to n) ≡ n
from-to≡id : ∀ (n : ℕ) → from (to n) ≡ n
from-to≡id zero = refl
from-to≡id (suc n) rewrite from-inc≡suc-from (to n) | from-to≡id n = refl

--------------------------------------------------------------------------------
--
-- RELATIONS
-- 
--------------------------------------------------------------------------------

-- exercise [orderings]

-- give an example of a preorder that is not a partial order
--   reachability in graphs 

-- give an example of a partial order that is not a preorder
--   equality

--------------------------------------------------------------------------------

-- exercise [≤-antisym-cases]

-- ≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
-- ≤-antisym z≤n z≤n = refl
-- ≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- the above proof omits cases where one argument is z≤n and one argument is s≤s
-- why is it ok to omit them?
--   because there is no constructor n≤z : ∀ {n: ℕ} → n ≤ zero

--------------------------------------------------------------------------------

-- exercise [*-mono-≤] (stretch)

-- generic definition of monotonicity
-- (just for fun)
monotonicity :
  (op : ℕ → ℕ → ℕ) →
  (op-comm : ∀ (a b : ℕ) → op a b ≡ op b a) →
  (r : ℕ → ℕ → Set) →
  (r-trans : ∀ {a b c : ℕ} → r a b → r b c → r a c) →
  (monoʳ : ∀ (m p q : ℕ) → r p q → r (op m p) (op m q)) →
  ∀ {m n p q : ℕ} →
  (r m n) →
  (r p q) →
  (r (op m p) (op n q))
monotonicity op op-comm r r-trans monoʳ {m} {n} {p} {q} mrn prq =
  r-trans (monoʳ m p q prq) (monoˡ m n q mrn)
    where monoˡ : ∀ (m n p : ℕ) → r m n → r (op m p) (op n p)
          monoˡ m n p rewrite op-comm m p | op-comm n p = monoʳ p m n

*-mono-≤ : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ = monotonicity _*_ *-comm _≤_ ≤-trans *-mono-≤ʳ
  where
    *-mono-≤ʳ : ∀ (m p q : ℕ) → p ≤ q → m * p ≤ m * q
    *-mono-≤ʳ zero _ _ _ = z≤n
    *-mono-≤ʳ (suc m) p q p≤q =
      +-mono-≤ {p} {q} {m * p} {m * q} p≤q (*-mono-≤ʳ m p q p≤q)

--------------------------------------------------------------------------------

-- exercise [<-trans] (recommended)

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n   : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

infix 4 _<_

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

--------------------------------------------------------------------------------

-- exercise [trichotomy]
-- (m < n) or (m ≡ n) or (m > n)

data Trichotomy (m n : ℕ) : Set where
  <-tri-< : m < n → Trichotomy m n
  <-tri-≡ : m ≡ n → Trichotomy m n
  <-tri-> : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = <-tri-≡ refl
<-trichotomy zero (suc n) = <-tri-< z<s
<-trichotomy (suc m) zero = <-tri-> z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | <-tri-< m<n = <-tri-< (s<s m<n)
... | <-tri-≡ m≡n = <-tri-≡ (cong suc m≡n)
... | <-tri-> m>n = <-tri-> (s<s m>n)

--------------------------------------------------------------------------------

-- exercise [+-mono-<]

+-mono-< : ∀ {m n p q : ℕ} → m < n → p < q → m + p < n + q
+-mono-< = monotonicity _+_ +-comm _<_ <-trans +-mono-<ʳ
  where
    +-mono-<ʳ : ∀ (m p q : ℕ) → p < q → m + p < m + q
    +-mono-<ʳ zero _ _ p<q = p<q
    +-mono-<ʳ (suc m) p q p<q = s<s (+-mono-<ʳ m p q p<q)

--------------------------------------------------------------------------------

-- exercise [≤-iff-<] (recommended)

-- show that suc m ≤ n implies m < n, and conversely

<-then-s≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-then-s≤ z<s = s≤s z≤n
<-then-s≤ (s<s m<n) = s≤s (<-then-s≤ m<n)

s≤-then-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
s≤-then-< {zero} (s≤s _) = z<s
s≤-then-< {suc _} (s≤s r) = s<s (s≤-then-< r)

--------------------------------------------------------------------------------

-- exercise [<-trans-revisited]

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited m<n n<p =
  s≤-then-< (≤-trans (<-then-s≤ m<n) (≤-trans n≤sn (<-then-s≤ n<p)))
    where
      n≤sn : ∀ {n : ℕ} → n ≤ suc n
      n≤sn {zero} = z≤n
      n≤sn {suc _} = s≤s n≤sn

--------------------------------------------------------------------------------

-- exercise [o+o≡e] (stretch)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n  → even (suc n)

data odd where
  suc  : ∀ {n : ℕ} → even n → odd  (suc n)

o+o≡e : ∀ {m n : ℕ} → odd m  → odd n → even (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd  (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)
e+o≡o zero on = on
e+o≡o (suc om) on = suc (o+o≡e om on)

--------------------------------------------------------------------------------

-- exercise [Bin-predicates] (stretch)

data One : Bin → Set
data Can : Bin → Set

data One where
  one : ∀ {b : Bin} → Can b → One (inc b)
  
data Can where
  zero : Can (x0 nil)
  suc : ∀ {b : Bin} → One b → Can b

-- show that increment preserves canonical bitstrings
one-inc : ∀ {b : Bin} → One b → One (inc b)
can-inc : ∀ {b : Bin} → Can b → Can (inc b)

one-inc (one cb) = one (can-inc cb)
can-inc zero = suc (one zero)
can-inc (suc ob) = suc (one-inc ob)

-- show that converting a natural to a bitstring always yields a canonical
-- bitstring
can-to : ∀ {n : ℕ} → Can (to n)
can-to {zero} = zero 
can-to {suc n} = suc (one (can-to {n}))

-- show that converting a canonical bitstring to a natural and back is the
-- identity

-- helper
can-from-inc≡suc-from : ∀ {b : Bin} → Can b → from (inc b) ≡ suc (from b)
can-from-inc≡suc-from {b} _ = from-inc≡suc-from b

one-to-from≡id : ∀ {b : Bin} → One b → to (from b) ≡ b
can-to-from≡id : ∀ {b : Bin} → Can b → to (from b) ≡ b

one-to-from≡id (one cb)
  rewrite can-from-inc≡suc-from cb  | can-to-from≡id cb = refl
can-to-from≡id zero = refl
can-to-from≡id osb@(suc ob)
  rewrite can-from-inc≡suc-from osb | one-to-from≡id ob = refl

\end{code}
