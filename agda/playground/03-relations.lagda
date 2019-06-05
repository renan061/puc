\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n   : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

-- _ = s≤s (s≤s (z≤n))
_ : 2 ≤ 4
_ = s≤s {1} {3} 1≤3
  where 1≤3 : 1 ≤ 3
        1≤3 = s≤s {0} {2} (z≤n {2})

infix 4 _≤_

-- exercises
-- give an example of a preorder that is not a partial order
--   => reachability in graphs 
-- give an example of a partial order that is not a total order
--   => equality

-- ≤ reflexivity
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n {zero}
≤-refl {suc n} = s≤s {n} {n} (≤-refl {n})
-- ≤-refl {zero}   =  z≤n
-- ≤-refl {suc n}  =  s≤s (≤-refl {n})

-- ≤ transitivity
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans {zero} {_} {p} _ _ = z≤n {p}
≤-trans {suc m} {suc n} {suc p} (s≤s m≤n) (s≤s n≤p) =
  s≤s {m} {p} (≤-trans {m} {n} {p} m≤n n≤p)
-- ≤-trans z≤n _ = z≤n
-- ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- ≤ anti-symmetry
≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- exercise ≤-antisym-cases
-- the above proof omits cases where one argument is z≤n and one
--   argument is s≤s. Why is it ok to omit them?
-- => because, ∀ m, m ≤ zero doesn't exist, and, therefore, there is
--   no proof to it

-- ≤ totality
data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n 
≤-total zero _ = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) = helper (≤-total m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward m≤n) = forward (s≤s m≤n)
    helper (flipped n≤m) = flipped (s≤s n≤m)

-- + ≤ monotonicity
-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

+-mono-r-≤ : ∀ (m p q : ℕ) → p ≤ q → m + p ≤ m + q
+-mono-r-≤ zero p q p≤q = p≤q
+-mono-r-≤ (suc m) p q p≤q = s≤s (+-mono-r-≤ m p q p≤q)

+-mono-l-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
-- +-monoˡ-≤ m n zero m≤n rewrite +-comm m zero | +-comm n zero = m≤n
-- +-monoˡ-≤ m n (suc p) m≤n
--  rewrite +-comm m (suc p) | +-comm n (suc p) = s≤s (+-monoʳ-≤ p m n m≤n)
+-mono-l-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-mono-r-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-mono-l-≤ m n p m≤n) (+-mono-r-≤ n p q p≤q)

-- exercise *-mono-≤ (stretch)
*-mono-r-≤ : ∀ (m p q : ℕ) → p ≤ q → m * p ≤ m * q
*-mono-r-≤ zero p q p≤q = z≤n
*-mono-r-≤ (suc m) p q p≤q =
  +-mono-≤ p q (m * p) (m * q) p≤q (*-mono-r-≤ m p q p≤q)

*-mono-l-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-mono-l-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-mono-r-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-mono-r-≤ m p q p≤q) (*-mono-l-≤ m n q m≤n)

-- generic definition of monotonicity
monotonicity :
  (op : ℕ → ℕ → ℕ) →
  (op-comm : ∀ (a b : ℕ) → op a b ≡ op b a) →
  (r : ℕ → ℕ → Set) →
  (r-trans : ∀ {a b c : ℕ} → r a b → r b c → r a c) →
  (mono-r : ∀ (m p q : ℕ) → r p q → r (op m p) (op m q)) →
  ∀ (m n p q : ℕ) →
  (r m n) →
  (r p q) →
  (r (op m p) (op n q))
monotonicity op op-comm r r-trans mono-r m n p q mrn prq =
  r-trans (mono-r m p q prq) (mono-l m n q mrn)
    where mono-l : ∀ (m n p : ℕ) → r m n → r (op m p) (op n p)
          mono-l m n p mrn rewrite op-comm m p | op-comm n p = mono-r p m n mrn

*-mono-≤′ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤′ m n p q m≤n p≤q =
  monotonicity _*_ *-comm _≤_ ≤-trans *-mono-r-≤ m n p q m≤n p≤q

-- strict inequality
infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n   : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

-- < transitivity
<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- < trichotomy
-- m < n, m ≡ n, or m > n

data Trichotomy (m n : ℕ) : Set where
  <-tri-< : m < n → Trichotomy m n
  <-tri-≡ : m ≡ n → Trichotomy m n
  <-tri-> : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = <-tri-≡ refl
<-trichotomy zero (suc n) = <-tri-< z<s
<-trichotomy (suc m) zero = <-tri-> z<s
<-trichotomy (suc m) (suc n) = helper (<-trichotomy m n)
  where
    helper : Trichotomy m n → Trichotomy (suc m) (suc n)
    helper (<-tri-< m<n) = <-tri-< (s<s m<n)
    helper (<-tri-≡ m≡n) = <-tri-≡ (cong suc m≡n)
    helper (<-tri-> m>n) = <-tri-> (s<s m>n)

-- exercise +-mono-<
+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q =
  monotonicity _+_ +-comm _<_ <-trans +-mono-r-< m n p q m<n p<q
    where
      +-mono-r-< : ∀ (m p q : ℕ) → p < q → m + p < m + q
      +-mono-r-< zero p q p<q = p<q
      +-mono-r-< (suc m) p q p<q = s<s (+-mono-r-< m p q p<q)

-- exercise ≤-iff-< : suc m ≤ n implies m < n, and conversely
<-then-s≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-then-s≤ z<s = s≤s z≤n
<-then-s≤ (s<s m<n) = s≤s (<-then-s≤ m<n)

s≤-then-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
-- s≤-then-< {zero} {zero} ()
s≤-then-< {zero} {suc _} (s≤s _) = z<s
-- s≤-then-< {suc m} {zero} ()
s≤-then-< {suc m} {suc n} (s≤s r) = s<s (s≤-then-< r)

<-then-≤ : ∀ {m n : ℕ} → m < n → m ≤ n
<-then-≤ {zero} {suc n} z<s = z≤n
<-then-≤ {suc m} {suc n} (s<s m<n) = s≤s (<-then-≤ m<n)

-- <-trans-revisited
<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited z<s (s<s n<p) = z<s
<-trans-revisited (s<s m<n) (s<s n<p) =
  s<s (s≤-then-< (≤-trans (<-then-s≤ m<n) (<-then-≤ n<p)))

-- even & odd
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n  → even (suc n)

data odd where
  suc  : ∀ {n : ℕ} → even n → odd  (suc n)

-- the sum of two even numbers is even
e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
-- the sum of an odd number and an even number is odd
o+e≡o : ∀ {m n : ℕ} → odd m  → even n → odd  (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)
o+e≡o (suc om) en = suc (e+e≡e om en)

-- exercise o+o≡e (stretch)
o+o≡e : ∀ {m n : ℕ} → odd m  → odd n → even (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd  (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)
e+o≡o zero on = on
e+o≡o (suc om) on = suc (o+o≡e om on)

-- bin-predicates (stretch)

-- binaries
data Bin : Set where
  nil : Bin
  x0_ : Bin -> Bin
  x1_ : Bin -> Bin

inc : Bin -> Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

data One : Bin → Set
data Can : Bin → Set

data One where
  one : ∀ {b : Bin} → Can b → One (inc b)
  
data Can where
  zero : Can nil
  suc : ∀ {b : Bin} → One b → Can b

-- increment preserves canonical bitstrings
inc-one : ∀ {b : Bin} → One b → One (inc b)
inc-can : ∀ {b : Bin} → Can b → Can (inc b)

inc-one (one cb) = one (inc-can cb)

inc-can zero = suc (one zero)
inc-can (suc ob) = suc (inc-one ob)

-- converting a natural to a bitstring always yields a canonical bitstring
to : ℕ → Bin
to zero = nil
to (suc n) = inc (to n)

to-can : ∀ {n : ℕ} → Can (to n)
to-can {zero} = zero 
to-can {suc n} = suc (one (to-can {n}))

-- converting a canonical bitstring to a natural and back is the identity
from : Bin → ℕ
from nil = zero
from (x0 b) = from b + from b
from (x1 b) = suc (from b + from b)

-- lema
from-inc≡suc-from : ∀ {b : Bin} → Can b → from (inc b) ≡ suc (from b)
from-inc≡suc-from {b} _ = helper b
  where
    helper : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
    helper nil = refl
    helper (x0 b) = refl
    helper (x1 b) =
      begin
        from (inc (x1 b))
      ≡⟨⟩
        from (x0 (inc b))
      ≡⟨⟩
        from (inc b) + from (inc b)
      ≡⟨ cong ((from (inc b)) +_) (helper b) ⟩
        from (inc b) + suc (from b)
      ≡⟨ cong (_+ (suc (from b))) (helper b) ⟩
        suc (from b) + suc (from b)
      ≡⟨⟩
        suc (from b + suc (from b))
      ≡⟨ cong suc (+-comm (from b) (suc (from b))) ⟩
        suc (suc (from b) + from b)
      ≡⟨⟩
        suc (suc (from b + from b))
      ≡⟨⟩
        suc (from (x1 b))
      ∎

one-to-from-id : ∀ {b : Bin} → One b → to (from b) ≡ b
can-to-from-id : ∀ {b : Bin} → Can b → to (from b) ≡ b

one-to-from-id (one cb) rewrite from-inc≡suc-from cb | can-to-from-id cb = refl

can-to-from-id zero = refl
can-to-from-id (suc ob)
  rewrite from-inc≡suc-from (suc ob) | one-to-from-id ob = refl 

\end{code}
