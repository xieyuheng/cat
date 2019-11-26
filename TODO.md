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
  - it feels like in category theory
    more is in the syntax of arrow
    explicit syntax helps to define syntax-based equality
    which helps to specify when we can not compose arrow
    (when error will occur)
- how to specify a new jojo like `pair` and `branch`?
  - to specify `f`
    we need to specify `x * f` and `f * x` for all x
  - thus to specify `pair` we need curry
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
