# Adventure

# Compare to category theory

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

- terminal object
  - in category
    ``` js
    { A : type -> unique f : { A -> unit_t } }
    drop : { A : type -> { A -> unit_t } } = { _ : A -> unit }
    drop(A) = { _ : A -> unit } : { A -> unit_t }
    ```
    the uniqueness of universal property
    just means `drop` is a function
  - in adventure
    { A -> id } in jojo is { (- A) }
    ``` js
    { A : type -> drop(A) : { (- A) } }
    drop : { [A : type] { (- A) } }
    A drop : { (- A) }
    cut(A drop) == { (- A) }
    cut(drop) == { [A : type] { (- A) } }
    ```
    this means that we can use `(- A)`
    to recover category theory from adventure
  - existence of `id(A)` in category theory is
    ``` js
    id : { A : type -> A }
    ```
    in adventure
    ``` js
    // the above `id` it will be
    id : { [A : type] A }
    // we can define a more general `id` in adventure
    id : {} = {}
    // to express "do nothing" more generally without a type parameter
    ```
# Implementation

- Implementation can be viewed as
  - evaluation (interpretation) of expression (syntax object)
  - model of theory

## env and ctx

- exp-t can form a adventure-t
- val-t can form a adventure-t only in ctx
  - mul : elem-t -> elem-t -> elem-t
  - val-mul : (ctx-t) -> (val-t, val-t) -> (val-t, ctx-t)
    state monad where the state is ctx-t
- eval is a functor from `exp-adventure` to `val-adventure in ctx`
  - how categorical semantics handles ctx?
- syntax `exp-adventure` is amost the abstract class itself
  this is why abstract class is called syntax or language
- so we have theory and model, just as in c-system
  and the model must be understand in ctx
