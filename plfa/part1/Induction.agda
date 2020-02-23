module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Exercise operators

-- a pair of operators that have an identity and are associative, commutative,
-- and distribute over one another.

max : ℕ → ℕ → ℕ
max 0 n = n
max n m = n + (m ∸ n)

-- max has an identity: from the first rule, 0 is the identity
-- max is associative: max(a, max(b, c)) = max(max(a, b), c) = max{a, b, c}
-- max is commutative: from the second rule we can change n, m wlog
-- * and max form the necessary pair because * distributes over max

-- an operator that has an identity and is associative but is not commutative.

_◦_ : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ)
(f ◦ g) x = f (g x)

-- ◦ has an identity: f(x) = x
-- ◦ is associative: f ◦ (g ◦ h) = (f ◦ g) ◦ h = f(g(h(x)))
-- ◦ is not commutative: for f(x) = x², g(x) = x + 2, (f ◦ g)(x) = (x + 2)²,
-- but (g ◦ f)(x) = x² + 2

-- Associativity and Comutativity with rewrite

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Exercise +-swap (recommended)

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc′ m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm′ m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc′ n m p ⟩
    n + (m + p)
  ∎

-- Exercise *-distrib-+ (recommended)

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc′ p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m) * p + n * p
  ∎

-- Exercise *-assoc (recommended)

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    (suc m) * (n * p)
  ∎

-- Exercise *-comm

*-null′ : ∀ (n : ℕ) → n * zero ≡ 0
*-null′ zero = refl
*-null′ (suc n) rewrite *-null′ n = refl

*-suc′ : ∀ (m n : ℕ) → m * (suc n) ≡ m * n + m
*-suc′ zero n = refl
*-suc′ (suc m) n =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ cong ((suc n) +_) (*-suc′ m n) ⟩
    (suc n) + (m * n + m)
  ≡⟨ sym (+-assoc′ (suc n) (m * n) m) ⟩
    ((suc n) + m * n) + m
  ≡⟨⟩
    (suc (n + m * n)) + m
  ≡⟨⟩
    (suc ((suc m) * n)) + m
  ≡⟨⟩
    suc ((suc m) * n + m)
  ≡⟨ cong suc (+-comm′ ((suc m) * n) m) ⟩
    suc (m + ((suc m) * n))
  ≡⟨⟩
    (suc m) + (suc m) * n
  ≡⟨ +-comm′ (suc m) ((suc m) * n) ⟩
    (suc m) * n + (suc m)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-null′ n = refl
*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + m * n
  ≡⟨ +-comm′ n (m * n) ⟩
    m * n + n
  ≡⟨ cong (_+ n) (*-comm m n) ⟩
    n * m + n
  ≡⟨ sym (*-suc′ n m) ⟩
    n * (suc m)
  ∎

-- Exercise 0∸n≡0

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 0 = refl
0∸n≡0 (suc n) = refl

-- Exercise ∸-+-assoc

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc 0 n p =
  begin
    0 ∸ n ∸ p
  ≡⟨ cong (_∸ p) (0∸n≡0 n) ⟩
    0 ∸ p
  ≡⟨ 0∸n≡0 p ⟩
    0
  ≡⟨ sym (0∸n≡0 (n + p)) ⟩
    0 ∸ (n + p)
  ∎
∸-+-assoc m 0 p rewrite +-identity′ p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

-- Exercise +*^

*-identity′ : ∀ (m : ℕ) → 1 * m ≡ m
*-identity′ 0 = refl
*-identity′ (suc m) rewrite *-comm 1 (suc m) | *-comm m 1 | *-identity′ m = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) →  m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m 0 p =
  begin
    m ^ (0 + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identity′ (m ^ p)) ⟩
    1 * (m ^ p)
  ≡⟨⟩
    (m ^ 0) * (m ^ p)
  ∎
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n 0 = refl
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ (suc p)
  ≡⟨⟩
    (m * n) * ((m * n) ^ p)
  ≡⟨ cong (_* ((m * n) ^ p)) (*-comm m n) ⟩
    (n * m) * ((m * n) ^ p)
  ≡⟨ cong ((n * m) *_) (^-distribʳ-* m n p) ⟩
    (n * m) * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*-assoc (n * m) (m ^ p) (n ^ p)) ⟩
    n * m * (m ^ p) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*-assoc n m (m ^ p)) ⟩
    n * (m * (m ^ p)) * (n ^ p)
  ≡⟨⟩
    n * (m ^ (suc p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*-comm n (m ^ (suc p))) ⟩
    (m ^ (suc p)) * n * (n ^ p)
  ≡⟨ *-assoc (m ^ (suc p)) n (n ^ p) ⟩
    (m ^ (suc p)) * (n * (n ^ p))
  ≡⟨⟩
    (m ^ (suc p)) * (n ^ (suc p))
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n 0 rewrite *-null′ n = refl
^-*-assoc m n (suc p) =
  begin
    (m ^ n) ^ (suc p)
  ≡⟨⟩
    (m ^ n) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
    m ^ (n + n * p)
  ≡⟨ cong (m ^_) (cong (n +_) (*-comm n p)) ⟩
    m ^ (n + p * n)
  ≡⟨⟩
    m ^ ((suc p) * n)
  ≡⟨ cong (m ^_) (*-comm (suc p) n) ⟩
    m ^ (n * (suc p))
  ∎

-- Exercise Bin-laws

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = 2 * (from bin)
from (bin I) = 1 + 2 * (from bin)

from-inc≡suc-from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc≡suc-from ⟨⟩ = refl
from-inc≡suc-from (b O) = refl
from-inc≡suc-from (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    2 * (from (inc b))
  ≡⟨ cong (2 *_) (from-inc≡suc-from b) ⟩
    2 * (suc (from b))
  ≡⟨ *-comm 2 (suc (from b)) ⟩
    (suc (from b)) * 2
  ≡⟨⟩
    2 + ((from b) * 2)
  ≡⟨ cong (2 +_) (*-comm (from b) 2) ⟩
    2 + (2 * (from b))
  ≡⟨⟩
    1 + 1 + (from (b O))
  ≡⟨ +-assoc′ 1 1 (from (b O)) ⟩
    1 + (1 + (from (b O)))
  ≡⟨⟩
    1 + (suc (from (b O)))
  ≡⟨⟩
    1 + (from (inc (b O)))
  ≡⟨⟩
    1 + (from (b I))
  ≡⟨⟩
    suc (from (b I))
  ∎

to-from : to (from (⟨⟩ O I)) ≡ ⟨⟩ I
to-from = refl

from-to : ∀ (n : ℕ) →  from (to n) ≡ n
from-to 0 = refl
from-to (suc n) rewrite from-inc≡suc-from (to n) | from-to n = refl
