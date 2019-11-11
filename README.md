# Cat

A categorical semantics library in Agda.

The aim of this library is to give semantics to inference rules of type theories, <br>
for examples,
- inductive types can be modeled by initial algebras,
- the validity of a group of introduction rules and elimination rule can be ensured by adjoint functors.

A consistent and scale-able coding style is important for keeping a software library maintainable. <br>
This is specially true for languages with strong syntax extension supports (like Agda). <br>
The preferred coding style of this library includes,
- prefer to use ASCII instead of unicode,
- prefer to use prefix notation instead of infix notation, except for syntax sugar,
- prefer to use `lisp-naming-convention` (see the following code example) instead of `camelCase`.

## Example

``` agda
record category-t (lv : level-t) : type (lsucc lv) where
  field
    object-t : type lv
    morphism-t : object-t -> object-t -> type lv
    id : (a : object-t) -> morphism-t a a
    compose : {a b c : object-t} ->
      morphism-t a b ->
      morphism-t b c ->
      morphism-t a c
    id-left : {a b : object-t} ->
      (f : morphism-t a b) ->
      the-eqv-t (morphism-t a b)
        (compose (id a) f) f
    id-right : {a b : object-t} ->
      (f : morphism-t a b) ->
      the-eqv-t (morphism-t a b)
        (compose f (id b)) f
    compose-associative : {a b c d : object-t} ->
      (f : morphism-t a b) ->
      (g : morphism-t b c) ->
      (h : morphism-t c d) ->
      the-eqv-t (morphism-t a d)
        (compose f (compose g h))
        (compose (compose f g) h)
```

## Community

- We enforce C4 as collaboration protocol.
  - [The C4 RFC](https://rfc.zeromq.org/spec:42/C4)
- [Style Guide](STYLE-GUIDE.md)
  - Observe the style of existing code and respect it.
- [Code of Conduct](CODE-OF-CONDUCT.md)

## License

- [GPLv3](LICENSE)
