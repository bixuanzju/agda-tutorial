module Views where

open import Data.Nat hiding (erase; compare)
open import Data.List
open import Data.Bool
open import Function hiding (_$_)
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Empty using (⊥-elim)


data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(suc (k * 2)) | odd k = k

infixr 30 _:all:_
data All {A : Set} (P : A → Set) : List A → Set where
  all[] : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = T (p x)

data Find {A : Set} (p : A → Bool) : List A → Set where
  found : (xs : List A) (y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs → Find p xs

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} (x : A) → Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} → x ≡ true → T x
trueIsTrue refl = _

falseIsFalse : {x : Bool} → x ≡ false → T (not x)
falseIsFalse refl = _

find : {A : Set} (p : A → Bool) (xs : List A) → Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with inspect (p x)
find p (x ∷ xs) | it false prf with find p xs
find p (x ∷ .(xs ++ y ∷ ys)) | it false prf | found xs y prf' ys = found (x ∷ xs) y prf' ys
find p (x ∷ xs) | it false prf | not-found prf' =  not-found (falseIsFalse prf :all: prf')
find p (x ∷ xs) | it true prf =  found [] x ( trueIsTrue prf) xs

data _∈_ {A : Set} (x : A) : List A → Set where
  hd : ∀ {xs} → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A} {x : A} {xs} → x ∈ xs → ℕ
index hd =  zero
index (tl prf) =  suc (index prf)

data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside : (x : A) (p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
[] ! n =  outside n
(x ∷ xs) ! zero =  inside x hd
(x ∷ xs) ! suc n with xs ! n
(x₁ ∷ xs) ! suc .(index p) | inside x p =  inside x (tl p)
(x ∷ xs) ! suc .(length xs + m) | outside m =  outside m


-- Ex 3.2
infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type → Type → Type

data _≠_ : Type → Type → Set where
  ı≠⇒ : ∀ {σ τ} → ı ≠ (σ ⇒ τ)
  ⇒≠ı : ∀ {σ τ} → (σ ⇒ τ) ≠ ı
  ⇒≠⇒₁ : ∀ {σ σ₁ τ τ₁} → σ ≠ σ₁ → (σ ⇒ τ) ≠ (σ₁ ⇒ τ₁)
  ⇒≠⇒₂ : ∀ {σ σ₁ τ τ₁} → τ ≠ τ₁ → (σ ⇒ τ) ≠ (σ₁ ⇒ τ₁)

data Equal? : Type → Type → Set where
  yes : ∀ {τ} → Equal? τ τ
  no : ∀ {σ τ} → σ ≠ τ → Equal? σ τ

_=?=_ : (σ τ : Type) → Equal? σ τ
ı =?= ı = yes
ı =?= (τ ⇒ τ₁) = no ı≠⇒
(σ ⇒ σ₁) =?= ı = no ⇒≠ı
(σ ⇒ σ₁) =?= (τ ⇒ τ₁) with σ =?= τ | σ₁ =?= τ₁
(τ ⇒ τ₁) =?= (.τ ⇒ .τ₁) | yes | yes = yes
(σ ⇒ σ₁) =?= (τ ⇒ τ₁) | no prf | _ = no (⇒≠⇒₁ prf)
(σ ⇒ σ₁) =?= (.σ ⇒ τ₁) | yes | no prf = no (⇒≠⇒₂ prf)

infixl 80 _$_
data Raw : Set where
  var : ℕ → Raw
  _$_ : Raw → Raw → Raw
  lam : Type → Raw → Raw

Ctx = List Type

data Term (Γ : Ctx) : Type → Set where
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (var x) =  var (index x)
erase (t $ u) =  erase t $ erase u
erase (lam σ t) =  lam σ (erase t)

data BadTerm (Γ : Ctx) : Set where
  var : (m : ℕ) → length Γ ≤ m → BadTerm Γ
  _$₁_ : Term Γ ı → Raw → BadTerm Γ
  _$₂_ψ_ : ∀ {σ σ' τ} → Term Γ (σ ⇒ τ) → Term Γ σ' → σ ≠ σ' → BadTerm Γ
  _$₃_ : ∀ {τ} → Term Γ τ → BadTerm Γ → BadTerm Γ
  _$₄_ : BadTerm Γ → Raw → BadTerm Γ
  lam : (σ : Type) → BadTerm (σ ∷ Γ) → BadTerm Γ

eraseBad : {Γ : Ctx} → BadTerm Γ → Raw
eraseBad (var m x) = var m
eraseBad (t $₁ u) = erase t $ u
eraseBad (t $₂ u ψ prf) = erase t $ erase u
eraseBad (t $₃ s) = erase t $ eraseBad s
eraseBad (t $₄ s) = eraseBad t $ s
eraseBad (lam σ t) = lam σ (eraseBad t)


data Infer (Γ : Ctx) : Raw → Set where
  ok : (τ : Type) (t : Term Γ τ) → Infer Γ (erase t)
  bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

n≤n+m : ∀ n m → n ≤ n + m
n≤n+m zero m = z≤n
n≤n+m (suc n) zero = s≤s (n≤n+m n zero)
n≤n+m (suc n) (suc m) = s≤s (n≤n+m n (suc m))

infer : (Γ : Ctx) (e : Raw) → Infer Γ e
infer Γ (var x) with Γ ! x
infer Γ (var .(index p)) | inside τ p = ok τ (var p)
infer Γ (var .(length Γ + m)) | outside m = bad (var (length Γ + m) (n≤n+m (length Γ) m))
infer Γ (s $ t) with infer Γ s
infer Γ (.(erase t) $ t₁) | ok ı t =  bad (t $₁ t₁)
infer Γ (.(erase t) $ t₁) | ok (τ ⇒ τ₁) t with infer Γ t₁
infer Γ (.(erase t₁) $ .(erase t)) | ok (τ₁ ⇒ τ₂) t₁ | ok τ t with τ₁ =?= τ
infer Γ (.(erase t₁) $ .(erase t)) | ok (τ ⇒ τ₂) t₁ | ok .τ t | yes =  ok τ₂ (t₁ $ t)
infer Γ (.(erase t₁) $ .(erase t)) | ok (τ₁ ⇒ τ₂) t₁ | ok τ t | no prf =  bad (t₁ $₂ t ψ prf)
infer Γ (.(erase t) $ .(eraseBad b)) | ok (τ ⇒ τ₁) t | bad b =  bad (t $₃ b)
infer Γ (.(eraseBad b) $ t) | bad b =  bad (b $₄ t)
infer Γ (lam τ t) with infer (τ ∷ Γ) t
infer Γ (lam τ .(erase t)) | ok τ₁ t = ok (τ ⇒ τ₁) (lam τ t)
infer Γ (lam τ .(eraseBad b)) | bad b = bad (lam τ b)


-- Ex 3.1
data Compare : ℕ → ℕ → Set where
  less : ∀ {n} k → Compare n (n + suc k)
  more : ∀ {n} k → Compare (n + suc k) n
  same : ∀ {n} → Compare n n

compare : (n m : ℕ) → Compare n m
compare zero zero = same
compare zero (suc m) = less m
compare (suc n) zero = more n
compare (suc n) (suc m) with compare n m
compare (suc n) (suc .(n + suc k)) | less k =  less k
compare (suc .(m + suc k)) (suc m) | more k =  more k
compare (suc m) (suc .m) | same = same

difference : ℕ → ℕ → ℕ
difference n m with compare n m
difference n .(n + suc k) | less k =  suc k
difference .(m + suc k) m | more k = suc k
difference m .m | same = zero

-- 3.2
lemma-All-∈ : ∀ {A x xs} {P : A → Set} → All P xs → x ∈ xs → P x
lemma-All-∈ all[] ()
lemma-All-∈ (x₂ :all: p) hd = x₂
lemma-All-∈ (x₂ :all: p) (tl i) = lemma-All-∈ p i

lem-filter-sound : {A : Set} (p : A → Bool) (xs : List A) →
                   All (satisfies p) (filter p xs)
lem-filter-sound p [] = all[]
lem-filter-sound p (x ∷ xs) with inspect (p x)
lem-filter-sound p (x ∷ xs) | it y prf with p x | prf
lem-filter-sound p (x ∷ xs) | it .false prf | false | refl = lem-filter-sound p xs
lem-filter-sound p (x ∷ xs) | it .true prf | true | refl =  trueIsTrue prf :all: lem-filter-sound p xs

lem-filter-complete : {A : Set} (p : A → Bool) (x : A) {xs : List A} →
                      x ∈ xs → satisfies p x → x ∈ filter p xs
lem-filter-complete p x hd px with inspect (p x)
lem-filter-complete p x hd px | it y prf with p x | prf
lem-filter-complete p x hd px | it .false prf | false | refl = ⊥-elim px
lem-filter-complete p x hd px | it y prf | true | c = hd
lem-filter-complete p x (tl {y} el) px with inspect (p y)
lem-filter-complete p x₁ (tl {y} el) px | it y₁ prf with p y | prf
lem-filter-complete p x₁ (tl el) px | it .false prf | false | refl = lem-filter-complete p x₁ el px
lem-filter-complete p x₁ (tl el) px | it y₁ prf | true | c = tl (lem-filter-complete p x₁ el px)
