module Universes where

data False : Set where
record True : Set where

data Bool : Set where
  true : Bool
  false : Bool

isTrue : Bool → Set
isTrue true = True
isTrue false = False

infix 30 not_
infixr 25 _and_

not_ : Bool → Bool
not true = false
not false = true

_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

notNotId : (a : Bool) → isTrue (not not a) → isTrue a
notNotId true prf = prf
notNotId false ()


data Functor : Set₁ where
  |Id| : Functor
  |K| : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|×|_ : Functor → Functor → Functor

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 50 _|+|_ _⊕_
infixr 60 _|×|_ _×_

[_] : Functor → Set → Set
[ |Id| ] X = X
[ |K| x ] X = x
[ F |+| G ] X =  [ F ] X ⊕ [ G ] X
[ F |×| G ] X = [ F ] X × [ G ] X

map : (F : Functor) → {X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
map |Id| f x = f x
map (|K| X) f x = x
map (F |+| G) f (inl x) =  inl (map F f x)
map (F |+| G) f (inr x) =  inr (map G f x)
map (F |×| G) f (x , y) = (map F f x) , (map G f y)

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) → μ F

mapFold : ∀ {X} F G → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
mapFold |Id| G φ < x > = φ (mapFold G G φ x)
mapFold (|K| A) G φ c = c
mapFold (F₁ |+| F₂) G φ (inl x) = inl (mapFold F₁ G φ x)
mapFold (F₁ |+| F₂) G φ (inr x) = inr (mapFold F₂ G φ x)
mapFold (F₁ |×| F₂) G φ (x , y) = mapFold F₁ G φ x , mapFold F₂ G φ y

fold : {F : Functor} {A : Set} → ([ F ] A → A) → μ F → A
fold {F} φ < x > = φ (mapFold F F φ x)

NatF = |K| True |+| |Id|
NAT = μ NatF

Z : NAT
Z = < inl _ >

S : NAT → NAT
S n = < inr n >

ListF = λ A → |K| True |+| (|K| A) |×| |Id|
LIST = λ A → μ (ListF A)

nil : {A : Set} → LIST A
nil = < inl _ >

cons : {A : Set} → A → LIST A → LIST A
cons x xs = < inr (x , xs) >

_ : LIST NAT
_ = cons Z (cons (S Z) nil)

[_||_] : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
[ f || g ] (inl x) = f x
[ f || g ] (inr x) = g x

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (x , y) = f x y

const : {A B : Set} → A  → B → A
const x y = x

foldr : {A B : Set} → (A → B → B) → B → LIST A → B
foldr {A}{B} f z = fold [ (const z) || (uncurry f) ]

plus : NAT → NAT → NAT
plus n m = fold [ const m || S ] n

open import Data.List hiding (_++_)
open import Data.Nat

data Type : Set where
  bool : Type
  nat : Type
  list : Type → Type
  pair : Type → Type → Type

El : Type → Set
El bool = Bool
El nat = ℕ
El (list a) = List (El a)
El (pair a b) = El a × El b

infix 30 _==_
_==_ : {a : Type} → El a → El a → Bool
_==_ {bool} true y = y
_==_ {bool} false y = not y

_==_ {nat} zero zero = true
_==_ {nat} zero (suc y) = false
_==_ {nat} (suc x) zero = false
_==_ {nat} (suc x) (suc y) = x == y

_==_ {list a} [] [] = true
_==_ {list a} [] (_ ∷ _) = false
_==_ {list a} (_ ∷ _) [] = false
_==_ {list a} (x ∷ xs) (y ∷ ys) = x == y and xs == ys

_==_ {pair a a₁} (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ and y₁ == y₂


-- Ex 3.4

open import Agda.Builtin.String
open import Data.String using (_++_)

Tag = String

mutual
  data Schema : Set where
    tag : Tag → List Child → Schema

  data Child : Set where
    text : Child
    elem : ℕ → ℕ → Schema → Child

-- In the same spirit as Fin n
data BList (A : Set) : ℕ → Set where
  [] : ∀ {n} → BList A n
  _::_ : ∀ {n} → A → BList A n → BList A (suc n)

data Cons (A B : Set) : Set where
  _::_ : A → B → Cons A B

FList : Set → ℕ → ℕ → Set
FList A zero m = BList A m
FList A (suc n) zero = False
FList A (suc n) (suc m) = Cons A (FList A n m)

open import Views using (All)

mutual
  data XML : Schema → Set where
    element : ∀ {kids} (t : Tag) → All Element kids → XML (tag t kids)

  Element : Child → Set
  Element text = String
  Element (elem n m s) = FList (XML s) n m

mutual
  printXML : {s : Schema} → XML s → String
  printXML (element t kids) =
    "<" ++ t ++ ">" ++ printChildren kids ++  "</" ++ t ++ ">"

  printChildren : {kids : List Child} → All Element kids → String
  printChildren {[]} All.all[] = ""
  printChildren {text ∷ kids} (y All.:all: ys) = y ++ printChildren ys
  printChildren {elem n m s ∷ kids} (y All.:all: ys) = printFList y ++ printChildren ys

  printFList : ∀ {n m s} → FList (XML s) n m → String
  printFList {zero} {m} f = printBList f
  printFList {suc n} {zero} ()
  printFList {suc n} {suc m} (s :: ss) = printXML s ++ printFList ss

  printBList : ∀ {m s} → BList (XML s) m → String
  printBList {zero} [] = ""
  printBList {suc m} [] = ""
  printBList {suc m} (x :: f) = printXML x ++ printBList f
