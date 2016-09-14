module AgdaBasics where

open import Data.Nat
open import Data.List

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)


data Image_∋_ {A B : Set} (f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

inv : {A B : Set} (f : A → B) (y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

magic : {A : Set} → Fin 0 → A
magic ()

infix 30 _!_
_!_ : {n : ℕ} {A : Set} → Vec A n → Fin n → A
cons x vs ! fzero = x
cons x vs ! fsuc n =  vs ! n

tabulate : {n : ℕ} {A : Set} → (Fin n → A) → Vec A n
tabulate {zero} f = nil
tabulate {suc n} f =  cons (f fzero) (tabulate (\x -> f (fsuc x)))

data False : Set where

record True : Set where

trivial : True
trivial = _

_<ℕ_ : ℕ → ℕ → 𝔹
_ <ℕ zero = false
zero <ℕ m = true
suc n <ℕ suc m = n <ℕ m

isTrue : 𝔹 → Set
isTrue true = True
isTrue flase = False

len : {A : Set} → List A → ℕ
len [] = zero
len (x ∷ ls) = suc (len ls)

lookup : {A : Set} (xs : List A) (n : ℕ) → isTrue (n <ℕ len xs) → A
lookup [] n ()
lookup (x ∷ xs) zero p = x
lookup (x ∷ xs) (suc n) p = lookup xs n p

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

leq-trans : {l m n : ℕ} → l ≤ m → m ≤ n → l ≤ n
leq-trans z≤n q = z≤n
leq-trans (s≤s p) (s≤s q) =  s≤s (leq-trans p q)

min : ℕ → ℕ → ℕ
min x y with x <ℕ y
min x y | true = x
min x y | false = y

filterL : {A : Set} → (A → 𝔹) → List A → List A
filterL p [] = []
filterL p (x ∷ ls) with p x
filterL p (x ∷ ls) | true = x ∷ filterL p ls
filterL p (x ∷ ls) | false = filterL p ls

data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ} → zero ≠ suc n
  s≠z : {n : ℕ} → suc n ≠ zero
  s≠s : {m n : ℕ} → m ≠ n → suc m ≠ suc n

data Equal? (n m : ℕ) : Set where
  eq : n == m → Equal? n m
  neq : n ≠ m → Equal? n m

equal? : (n m : ℕ) → Equal? n m
equal? zero zero = eq refl
equal? zero (suc m) = neq z≠s
equal? (suc n) zero = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m) | neq x = neq (s≠s x)

infix 20 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  left : forall {xs y ys} → xs ⊆ ys → xs ⊆ (y ∷ ys)
  keep : forall {x y xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (y ∷ ys)

lem-filter : {A : Set} (p : A → 𝔹) (xs : List A) → filterL p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x ∷ xs) with p x
lem-filter p (x ∷ xs) | true =  keep (lem-filter p xs)
lem-filter p (x ∷ xs) | false = left (lem-filter p xs)

lem-plus-zero : (n : ℕ) → (n + zero) == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
lem-plus-zero (suc n) | .n | refl = refl


module M where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

  maybe : {A B : Set} → B → (A → B) → Maybe A → B
  maybe b f nothing = b
  maybe b f (just x) = f x

record Point : Set where
  constructor _,_
  field x : ℕ
        y : ℕ

mkPoint : ℕ → ℕ → Point
mkPoint a b = a , b

record Monad (M : Set → Set) : Set1 where
  field
    return : {A : Set} → A → M A
    _>>=_ : {A B : Set} → M A → (A → M B) → M B

  mapLM : {A B : Set} → (A → M B) → List A → M (List B)
  mapLM f [] =  return []
  mapLM f (x ∷ xs) =  f x >>= (\y -> mapLM f xs >>= \ys -> return (y ∷ ys))

-- Ex 2.2
lem-!-tab : forall {A n} (f : Fin n → A) (i : Fin n) →  (tabulate f) ! i  == f i
lem-!-tab f fzero = refl
lem-!-tab f (fsuc i) = lem-!-tab (\s → f (fsuc s)) i

lem-tab-! : forall {A n} (xs : Vec A n) → tabulate (_!_ xs) == xs
lem-tab-! nil = refl
lem-tab-! (cons x xs) with tabulate (_!_ xs) | lem-tab-! xs
lem-tab-! (cons x xs) | .xs | refl = refl

-- Ex 2.3
⊆-refl : {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl {xs = []} = stop
⊆-refl {xs = x ∷ xs} = keep (⊆-refl {xs = xs})

⊆-trans : {A : Set} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans stop q = q
⊆-trans (left p) (left q) =  left (⊆-trans (left p) q)
⊆-trans (left p) (keep q) =  left (⊆-trans p q)
⊆-trans (keep p) (left q) =  keep (⊆-trans (left p) q)
⊆-trans (keep p) (keep q) = keep (⊆-trans p q)

infixr 30 _::_
data SubList {A : Set} : List A → Set where
  [] : SubList []
  _::_ : forall x {xs} → SubList xs → SubList (x ∷ xs)
  skip : forall {x xs} → SubList xs → SubList (x ∷ xs)

forget : {A : Set} {xs : List A} → SubList xs → List A
forget [] = []
forget (x :: s) =  x ∷ forget s
forget (skip s) =  forget s

lem-forget : {A : Set} {xs : List A} (zs : SubList xs) → forget zs ⊆ xs
lem-forget [] = stop
lem-forget (x :: zs) =  keep (lem-forget zs)
lem-forget (skip zs) =  left (lem-forget zs)

filter' : {A : Set} → (A → 𝔹) → (xs : List A) → SubList xs
filter' p [] = []
filter' p (x ∷ xs) with p x
filter' p (x ∷ xs) | true =  skip (filter' p xs)
filter' p (x ∷ xs) | false =  x :: (filter' p xs)

complement : {A : Set} {xs : List A} → SubList xs → SubList xs
complement {xs = []} [] = []
complement {xs = .x ∷ xs} (x :: zs) =  skip (complement zs)
complement {xs = x ∷ xs} (skip zs) =  x :: complement zs

subLists : {A : Set} (xs : List A) → List (SubList xs)
subLists [] = [ [] ]
subLists (x ∷ xs) = concatMap (\s → skip s ∷ [ x :: s ]) (subLists xs)
