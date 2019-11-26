# adventure
- can we use universal property in adventure?
  - "universal" is about "uniqueness" and "forall"
  - how to define `pair`?
    we need `not-eqv-t` to specify that
    `x * fst == error`
    if `x` is not a `pair`
  - we need `not-eqv-t` to specify that
    `a * (- b) == error`
    if `a != b`
- what is a functor?
  a map that respect `mul` and `cut`?
  - (fun (x * y)) == ((fun x) * (fun y))
    (cut (fun x)) == (fun (cut x))
  - `quo` does not respect `mul`
    (quo (x * y)) != ((quo x) * (quo y))
  - `-` is a functor
    (- (x * y)) == ((- x) * (- y))
    (cut (- x)) == (- (cut x))
# category
- `cone-t` and `limit-t` -- by natural transformation
- how to handle dual construction?
- abstract `unique`
# structure
- group-category
- abelian-group-t
- ring-t
- semiring-t
- orders
- lattice-t
# semantics
- example semantics for simply typed lambda calculus
