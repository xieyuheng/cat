module RBT where

  data Order : Set where
    Equal : Order
    Less : Order
    Greater : Order

  module RBT
    (Key : Set)
    (compare : Key -> Key -> Order)
    (Value : Set) where

    data Color : Set where
      Red : Color
      Black : Color

    data Tree : Set where
      Empty
        : Tree
      Node
        : (l : Tree) ->
          (c : Color) ->
          (kv : (Key , Value)) ->
          (r : Tree) -> Tree

    blackenRoot : Tree -> Tree
    blackenRoot Empty = Empty
    blackenRoot (Node l c kv r) = Node l Black kv r

    balance
      : Tree ->
        (c : Color) ->
        (kv : (Key , Value)) ->
        Tree -> Tree
    balance (Node (Node a Red x b) Red y c) Black z d =
      Node (Node a Black x b) Red y (Node c Black z d)
    balance (Node a Red x (Node b Red y c)) Black z d =
      Node (Node a Black x b) Red y (Node c Black z d)
    balance a Black x (Node (Node b Red y c) Red z d) =
      Node (Node a Black x b) Red y (Node c Black z d)
    balance a Black x (Node b Red y (Node c Red z d)) =
      Node (Node a Black x b) Red y (Node c Black z d)
    balance l c kv r = Node l c kv r

    -- ins : Tree -> (kv : (Key , Value)) -> Tree
    -- ins Empty kv = Node Empty Red kv Empty
    -- ins (Node l c (k', v') r) (k, v) =
    --   case compare k k' of
    --     Equal => Node l c (k, v) r
    --     Less => balance (ins l (k, v)) c (k', v') r
    --     Greater => balance l c (k', v') (ins r (k, v))

    ins : Tree -> (kv : (Key , Value)) -> Tree
    ins Empty kv = Node Empty Red kv Empty
    ins (Node l c (k', v') r) (k, v) with (compare k k')
    ... | Equal = Node l c (k, v) r
    ... | Less = balance (ins l (k, v)) c (k', v') r
    ... | Greater = balance l c (k', v') (ins r (k, v))

    insert : Tree -> (Key , Value) -> Tree
    insert t kv = blackenRoot (ins t kv)

    -- invariants of red-black-tree --
    -- t is a red-black-tree iff
    -- (1) t has a black-height
    --     i.e. every path from root to leaf
    --          has the same numebr of black nodes
    -- (2) t is well-red
    --     i.e. no red node has a red child

    data HasBH : Tree -> Nat -> Set where
      EmptyHasBH
        : HasBH Empty 1
      RedNodeHasBH
        : (hl : HasBH l n) ->
          (hr : HasBH r n) ->
          HasBH (Node l Red kv r) n
      BlackNodeHasBH
        : (hl : HasBH l n) ->
          (hr : HasBH r n) ->
          HasBH (Node l Black kv r) (S n)

    -- blackenRootHasBH
    --   : HasBH t n ->
    --     (m : Nat ** HasBH (blackenRoot t) m)
    -- blackenRootHasBH {t = Empty} h = (1 ** EmptyHasBH)
    -- blackenRootHasBH {t = (Node l Red kv r)} {n} (RedNodeHasBH hl hr) =
    --   ((S n) ** (BlackNodeHasBH hl hr))
    -- blackenRootHasBH {t = (Node l Black kv r)} {n} h = (n ** h)

    -- remember to case analyze dependently typed data first
    --   in the about example, the data would be `h`
