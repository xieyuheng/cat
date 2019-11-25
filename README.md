# Cat -- A categorical semantics library in Agda

**[Work in progress, but you can star it first.]**

The aim of this library is to provide semantics to type theories. <br>
For examples,
- inductive types can be modeled by initial algebras,
- the validity of a group of introduction rules and elimination rule can be ensured by adjoint functors.

## Using inconsistent system

The inconsistent `type-in-type` system is used.

An inconsistent system is still very valuable for creative reasoning, <br>
and we can always use a consistent system later in the development.

This argument is like the argument against premature optimization in programming.

- More about using inconsistent system, <br>
  see [Vladimir Voevodsky's Lecture about Univalent Foundations at the Institut Henri Poincaré](https://inner.xieyuheng.now.sh/person/vladimir-voevodsky/lecture-about-univalent-foundations-at-the-institut-henri-poincar%C3%A9).

## Coding style

A consistent and scale-able coding style is important for keeping a software library maintainable. <br>
This is specially true for languages with strong syntax extension supports (like Agda). <br>
The preferred coding style of this library includes,
- prefer to use ASCII instead of unicode,
- prefer to use prefix notation instead of infix notation, except for syntax sugar,
- prefer to use `lisp-naming-convention` (see the following code example) instead of `camelCase`.

## Example

``` agda
record category-t : type where
  field
    object-t : type
    morphism-t : object-t -> object-t -> type
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

Contributions are welcome, see [current TODO list](TODO.md) for tasks. <br>
(Please add yourself to [the AUTHORS list](AUTHORS) if you made any contributions.)

- We enforce C4 as collaboration protocol.
  - [The C4 RFC](https://rfc.zeromq.org/spec:42/C4)
- [Style Guide](STYLE-GUIDE.md)
  - Observe the style of existing code and respect it.
- [Code of Conduct](CODE-OF-CONDUCT.md)

## License

- [GPLv3](LICENSE)
