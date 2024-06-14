open import Level
open import Function
open import Data.Bool
open import Data.List
open import Data.Product
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.HeterogeneousEquality

NSet : {a : Level} -> Set a -> Set a
NSet A = A -> Bool

_∪_ : {a : Level} -> {A : Set a} -> NSet A -> NSet A -> NSet A
_∪_ s1 s2 = \ e -> s1 e ∨ s2 e

_∩_ : {a : Level} -> {A : Set a} -> NSet A -> NSet A -> NSet A
_∩_ s1 s2 = \ e -> s1 e ∧ s2 e

⋂ : {a : Level} -> {A : Set a} -> List (NSet A) -> NSet A
⋂ [] _ = false
⋂ (x ∷ []) = x
⋂ (x ∷ xs) = x ∩ ⋂ xs

_∈_ : {a : Level} -> {A : Set a} -> A -> NSet A -> Set
_∈_ e s = true ≅ s e

_⊆_ : {a : Level} -> {A : Set a} -> NSet A -> NSet A -> Set a
_⊆_ {_} {A} s1 s2 = (e : A) -> e ∈ s1 -> e ∈ s2

_⊂_ : {a : Level} -> {A : Set a} -> NSet A -> NSet A -> Set a
_⊂_ = {!!}

-- | @P S@ is the power set of @S@.  Equivalently, @P S@ is the set of all subsets of @S@.
P : {a : Level} -> {A : Set a} -> NSet A -> NSet (NSet A)
P = {!!}

-- | Any value @t@ of type @Topology N@ is a topology on @N@.  @Topology.collection N@ is @t@'s collection, and the other fields indicate that @t@ really is a topology.
record Topology {a : Level}
                {A : Set a}
                (N : NSet A) : Set (Level.suc a) where
  field
    collection : NSet (NSet A)
    hasEmptySet : (\ _ -> false) ∈ collection
    hasN : N ∈ collection
    hasUnion : (s1 s2 : NSet A) ->
               s1 ∈ collection ->
               s2 ∈ collection ->
               (s1 ∪ s2) ∈ collection
    hasIntersection : (s : List (NSet A)) ->
                      All (\ e -> e ∈ collection) s ->
                      ⋂ s ∈ collection

discreteTopology : {a : Level} -> {A : Set a} -> (N : NSet A) -> Topology N
discreteTopology N = record
  {collection = P N
  ;hasN = {!!}
  ;hasEmptySet = {!!}
  ;hasUnion = {!!}
  ;hasIntersection = {!!}
  }

indiscreteTopology : {a : Level} -> {A : Set a} -> (N : NSet A) -> Topology N
indiscreteTopology {a} {A} N = record
  {collection = f
  ;hasN = {!!}
  ;hasEmptySet = {!!}
  ;hasUnion = {!!}
  ;hasIntersection = {!!}
  }
  where
  f = {!!}
  recognizesNothingElse :
    (n : NSet A) ->
    n ≇ N ->
    n ≇ (\ (_ : A) -> false) ->
    false ≅ f n
  recognizesNothingElse = {!!}
  
_isFinerThan_ : {a : Level} ->
                {A : Set a} ->
                {N : NSet A} ->
                Topology N ->
                Topology N ->
                Set _
t1 isFinerThan t2 = Topology.collection t2 ⊆ Topology.collection t1

record Basis {a : Level}
             {A : Set a}
             (N : NSet A) : Set a where
  field
   elements : NSet (NSet A)
   allContainedByBasisElements :
     (e : A) ->
     e ∈ N ->
     Σ (NSet A) (\ n -> e ∈ n × n ∈ elements)
   multiContainmentImpliesProperSubset :
     (e : A) ->
     e ∈ N ->
     (n1 n2 : NSet A) ->
     e ∈ (n1 ∩ n2) ->
     Σ (NSet A) (\ n3 -> n3 ⊂ (n1 ∩ n2) × n3 ∈ elements)
