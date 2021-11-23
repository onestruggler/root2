{-# OPTIONS --without-K --safe #-}

module root2 where

-- imports. We use the latest agda stdlib. 
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum renaming (inj₁ to even ; inj₂ to odd)
open import Relation.Nullary
open import Data.Empty

--  We show √2 is irrational. The following theorem says there

-- Even predicate.
Even : ℕ -> Set
Even n = ∃ λ k → n ≡ 2 * k

-- Odd predicate.
Odd : ℕ -> Set
Odd n = ∃ λ k → n ≡ 1 + 2 * k


open +-*-Solver

-- Lemma: a natural number cannot be both even and odd.
lemma-even-odd-exclusive : ∀ k l ->  ¬ 2 * k ≡ 1 + 2 * l
lemma-even-odd-exclusive k l hyp = z hyp'
  where
    z : ¬ 0 ≡ 1
    z ()

    n*m%n≡0 : ∀ m n .{{_ : NonZero n}} → (n * m) % n ≡ 0
    n*m%n≡0 m n = begin
        (n * m) % n ≡⟨ cong (_% n) (solve 2 (λ n m → n :* m := m :* n) refl n m) ⟩
        (m * n) % n ≡⟨ m*n%n≡0 m n ⟩
        0 ∎
        where
          open ≡-Reasoning
      
          
    lem1%2 : 1 % 2 ≡ 1
    lem1%2 = refl 
    
    hyp' : 0 ≡ 1
    hyp' =  begin
        0 ≡⟨ sym (n*m%n≡0 k 2)  ⟩ 
        (2 * k) % 2 ≡⟨ cong (_% 2) hyp ⟩ 
        (1 + 2 * l) % 2 ≡⟨ %-distribˡ-+ 1 (2 * l) 2 ⟩
        ((1 % 2) + ((2 * l) % 2)) % 2 ≡⟨ cong (_% 2) (cong₂ (_+_) lem1%2 (n*m%n≡0 l 2)) ⟩
        (1 + 0) % 2 ≡⟨ refl ⟩
        1 % 2 ≡⟨ refl ⟩
        1 ∎
        where
          open ≡-Reasoning      


lemma-even-odd-exclusive' : ∀ n -> ¬ (Even n × Odd n)
lemma-even-odd-exclusive' n ((k , eqn) , (l , eqn')) = lemma-even-odd-exclusive k l claim
  where
    claim : 2 * k ≡ 1 + 2 * l
    claim = begin
        2 * k ≡⟨ sym eqn ⟩
        n ≡⟨ eqn' ⟩ 
        1 + 2 * l ∎
        where
          open ≡-Reasoning
      


-- Lemma: a natrual number is either even or odd (but not both as shown by lemma-even-odd-exclusive').
Parity : (n : ℕ) -> Even n ⊎ Odd n
Parity zero = even (zero , refl)
Parity (suc n) with Parity n
... | even (k , eq) = odd (k , cong suc eq)
... | odd (k , eq) = even (suc k , claim)
  where
    claim : suc n ≡ suc (k + suc (k + 0))
    claim = begin
      suc n ≡⟨ refl ⟩
      1 + n ≡⟨ cong (1 +_) eq ⟩ 
      1 +  suc (k + (k + 0)) ≡⟨ solve 1 (λ k → con 1 :+ (con 1 :+ (k :+ (k :+ con 0))) := con 1 :+ (k :+ (con 1 :+ (k :+ con 0)))) refl k ⟩
      1 + (k + (1 + (k + 0))) ≡⟨ refl ⟩
      suc (k + suc (k + 0)) ∎
      where
        open ≡-Reasoning
    

lemma-div2 : ∀ n .{{_ : NonZero n}} -> n / 2 < n
lemma-div2 n = m/n<m n 2 (s≤s (s≤s z≤n))


lemma-<-< : ∀ {a b c} -> a < b -> b < suc c -> a < c
lemma-<-<  (s≤s ab) (s≤s bc) = <-transˡ (s≤s ab) bc

lemma-div2' : ∀ n b .{{_ : NonZero n}} -> n < 1 + b -> n / 2 < b
lemma-div2' n b n1b = lemma-<-< (lemma-div2 n) n1b

-- We do a case split in the parity of m and n. For each of the four
-- cases, we can derive a contradiction using induction on the bound
-- of m and n.
lemma-root2-irra : ∀ b m n -> ¬ m ≡ 0 -> ¬ n ≡ 0 → m < b → n < b → ¬ m * m ≡ 2 * (n * n)
lemma-root2-irra (suc b) 0 0 mnz nnz mlb nlb hyp = mnz refl 
lemma-root2-irra (suc b) 0 (suc n) mnz nnz mlb nlb hyp = mnz refl 
lemma-root2-irra (suc b) (suc m) 0 mnz nnz mlb nlb hyp = nnz refl 
lemma-root2-irra (suc b) m@(suc m') n@(suc n') mnz nnz mlb nlb hyp with Parity m | Parity n
... | even (k , eqm) | even (l , eqn) = ih
  where
    factor-four : 4 * (k * k) ≡ 4 * (2 * (l * l))
    factor-four = begin
      4 * (k * k) ≡⟨ solve 1 (λ k → con 4 :* (k :* k) := (con 2 :* k) :* (con 2 :* k)) refl k ⟩
      (2 * k) * (2 * k) ≡⟨ cong₂ _*_ (sym eqm) (sym eqm) ⟩
      m * m ≡⟨ hyp ⟩
      2 * (n * n) ≡⟨ cong (2 *_) (cong₂ _*_ eqn eqn) ⟩
      2 * ((2 * l) * (2 * l)) ≡⟨ solve 1 (λ l → con 2 :* ((con 2 :* l) :* (con 2 :* l)) := con 4 :* (con 2 :* (l :* l))) refl l ⟩
      4 * (2 * (l * l)) ∎
      where
        open ≡-Reasoning
    
        
    hyp' : k * k ≡ 2 * (l * l)
    hyp' = *-cancelˡ-≡ 4 factor-four
    
    klb : k < b
    klb = begin-strict
      k ≡⟨ sym (m*n/n≡m k 2) ⟩
      (k * 2) / 2 ≡⟨ cong (_/ 2) (solve 1 (λ k → k :* con 2 := con 2 :* k) refl k) ⟩ 
      (2 * k) / 2 ≡⟨ cong (_/ 2) (sym eqm) ⟩ 
      m / 2 <⟨ lemma-div2' m b mlb ⟩ 
      b ∎
      where
        open ≤-Reasoning
    

    llb : l < b
    llb = begin-strict
      l ≡⟨ sym (m*n/n≡m l 2) ⟩
      (l * 2) / 2 ≡⟨ cong (_/ 2) (solve 1 (λ l → l :* con 2 := con 2 :* l) refl l) ⟩ 
      (2 * l) / 2 ≡⟨ cong (_/ 2) (sym eqn) ⟩ 
      n / 2 <⟨ lemma-div2' n b nlb ⟩ 
      b ∎
      where
        open ≤-Reasoning
    

    knz : ¬ k ≡ 0
    knz k0 = mnz m0
      where
      m0 : m ≡ 0
      m0 = begin
        m ≡⟨ eqm ⟩
        2 * k ≡⟨ cong (2 *_) k0 ⟩ 
        2 * 0 ≡⟨ refl ⟩ 
        0 ∎
        where
          open ≡-Reasoning
      


    lnz : ¬ l ≡ 0
    lnz l0 = nnz n0
      where
      n0 : n ≡ 0
      n0 = begin
        n ≡⟨ eqn ⟩
        2 * l ≡⟨ cong (2 *_) l0 ⟩ 
        2 * 0 ≡⟨ refl ⟩ 
        0 ∎
        where
          open ≡-Reasoning
      

    ih : ⊥
    ih = lemma-root2-irra b k l knz lnz klb llb hyp'


... | even (k , eqm) | odd (l , eqn) = lemma-even-odd-exclusive' (n * n) (even-right , odd-right)
  where
    even-left : Even (m * m)
    even-left = 2 * (k * k) , claim
      where
        claim : m * m ≡ 2 * (2 * (k * k)) 
        claim = begin
          m * m ≡⟨ cong₂ _*_ eqm eqm ⟩
          (2 * k) * (2 * k) ≡⟨ solve 1 (λ k → (con 2 :* k) :* (con 2 :* k) := con 2 :* (con 2 :* (k :* k))) refl k ⟩
          2 * (2 * (k * k)) ∎
            where
              open ≡-Reasoning
          

    odd-right : Odd (n * n)
    odd-right = (2 * (l * l) + 2 * l) , claim
      where
        claim : n * n ≡ 1 + 2 * (2 * (l * l) + 2 * l) 
        claim = begin
          n * n ≡⟨ cong₂ _*_ eqn eqn ⟩
          (1 + 2 * l) * (1 + 2 * l) ≡⟨ solve 1 (λ l → (con 1 :+ con 2 :* l) :* (con 1 :+ con 2 :* l) := con 1 :+ (con 2 :* ((con 2 :* (l :* l)) :+ con 2 :* l))) refl l ⟩
          1 + 2 * (2 * (l * l) + 2 * l)  ∎
            where
              open ≡-Reasoning
          

    2*n*n≡2*2*k*k : 2 * (n * n) ≡ 2 * (2 * (k * k))
    2*n*n≡2*2*k*k = begin
          2 * (n * n) ≡⟨ sym hyp ⟩
          m * m ≡⟨ (let (_ , p) = even-left in p) ⟩
          2 * (2 * (k * k)) ∎
            where
              open ≡-Reasoning
          
    n*n≡2*k*k : (n * n) ≡ (2 * (k * k))
    n*n≡2*k*k = *-cancelˡ-≡ 2 2*n*n≡2*2*k*k

    even-right : Even (n * n)
    even-right = k * k , (n*n≡2*k*k)

... | odd (k , eqn) | _  = lemma-even-odd-exclusive' (m * m) (even-left , odd-left)
  where
    odd-left : Odd (m * m)
    odd-left = (2 * (k * k) + 2 * k) , claim
      where
        claim : m * m ≡ 1 + 2 * (2 * (k * k) + 2 * k) 
        claim = begin
          m * m ≡⟨ cong₂ _*_ eqn eqn ⟩
          (1 + 2 * k) * (1 + 2 * k) ≡⟨ solve 1 (λ k → (con 1 :+ con 2 :* k) :* (con 1 :+ con 2 :* k) := con 1 :+ (con 2 :* ((con 2 :* (k :* k)) :+ con 2 :* k))) refl k ⟩
          1 + 2 * (2 * (k * k) + 2 * k)  ∎
            where
              open ≡-Reasoning

    even-left : Even (m * m)
    even-left = (n * n) , hyp
    

-- Main theorem: for any natural number m and n, it impossible that m
-- * m ≡ 2 * (n * n) except when m ≡ 0 and n ≡ 0 (in this situation,
-- m/n is not defined), in other words, no rational number equals √2.
theorem-root2-irra : ∀ m n ->  m * m ≡ 2 * (n * n) -> m ≡ 0 × n ≡ 0
theorem-root2-irra zero zero hyp = (refl , refl )
theorem-root2-irra zero n@(suc n') hyp = (refl , sym 0≡n )
  where
    2*0≡2*n*n : 2 * 0 ≡ 2 * (n * n)
    2*0≡2*n*n = hyp
    0≡n*n : 0 ≡ n * n
    0≡n*n = *-cancelˡ-≡ 2 hyp
    n*0≡n*n : n * 0 ≡ n * n
    n*0≡n*n = begin
          n * 0 ≡⟨ *-comm n 0 ⟩
          0 * n ≡⟨ refl ⟩
          0  ≡⟨ 0≡n*n ⟩
          n * n  ∎
            where
              open ≡-Reasoning

    0≡n : 0 ≡ n
    0≡n = *-cancelˡ-≡ n n*0≡n*n

theorem-root2-irra m@(suc m') n@(suc n') hyp = ⊥-elim claim
  where
    -- m ⊔ n = max m n  
    b = 1 + (m ⊔ n)
    mlb : m < b
    mlb = s≤s (m≤m⊔n m n)
    nlb : n < b
    nlb = s≤s (m≤n⊔m m n)
    claim = lemma-root2-irra b m n (λ ()) (λ ()) mlb nlb hyp
