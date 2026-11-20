# Closed type families

A closed type family computes an ordinary Jihoo type from one concrete
input type. Write its equations together in a `type` declaration. The
compiler takes the first matching equation and uses the resulting type
wherever the application appeared. Imports can use a public family and
its rules always come from its defining module.

## Deriving the other end of a protocol

Suppose a client sends a string, waits for a number and finishes. Its peer
must receive that string before sending the number. The following types
describe the two actions and the protocol that follows each one.

```jihoo
struct End {}
struct Send(A: type, K: type) {}
struct Recv(A: type, K: type) {}

type Dual {
    End => End
    Send(let A, let K) => Recv(A, Dual(K))
    Recv(let A, let K) => Send(A, Dual(K))
}

type Client = Send(String, Recv(u32, End))
type Server = Recv(String, Send(u32, End))

fn peer(plan: Dual(Client)) -> Server { plan }
fn round_trip(plan: Dual(Dual(Client))) -> Client { plan }
```

The first reduction turns the outer `Send` into `Recv` and keeps its
`String` payload. The recursive call turns the next `Recv` into `Send`
and the `End` equation stops the calculation. That gives exactly
`Recv(String, Send(u32, End))`, so `peer` can return its input directly.
Changing just the reply in `Client` to `u64` makes that return a type error.
Applying `Dual` twice to this protocol reconstructs `Client`.

A protocol can also give one side a choice. For constructors `Choose(L, R)`
and `Offer(L, R)`, add two equations that swap the constructors and take the
dual of each branch. An API can then consume an owned endpoint in a `sink`
parameter and return an endpoint at its next state. The type family checks
the two descriptions agree. Jihoo's move checker catches a second use of
the old endpoint. The example exercises these rules with messages.
[Runnable protocol example](../../examples/session_duality.jh)

## Pattern matching

- `let T` binds the current argument for this equation. Another `let T`
  in the same pattern requires an equal argument. Each `_` matches
  independently.
- Struct and enum patterns inspect their declared generic arguments. Two
  declarations with the same spelling in different modules have distinct
  identities. Spell the declared name in the pattern. Aliases of that
  type in the input expand before matching.
- Tuple, array, slice, pointer, `ref` and `inout` patterns decompose their
  type constructors. `[let T; let N]` binds the element type and the
  compile-time length. Integer and boolean literals can select particular
  compile-time arguments.
- Rules can overlap. A final `_` supplies a default. Without a matching
  equation, applying the family produces a compile error at the use site.

For example, a pair of identical types can select an array representation.
The second equation preserves any other input.

```jihoo
type Compact {
    (let T, let T) => [T; 2]
    let T => T
}

fn samples() -> Compact((u8, u8)) { [4, 9] }
fn reading() -> Compact((u8, bool)) { (4, true) }
```

Pattern names are local to their equation. The selected right-hand side is
resolved in the module that defines the family. Use `pub type` to export a
family and `module.Name(T)` to apply it from a caller.

## Reduction and inference

Jihoo evaluates a family after its input type is known. For a signature
such as `f(comptime P: type, x: Endpoint(P), y: Endpoint(Dual(P)))`, it
can infer `P` from `x`, compute `Dual(P)`, and check `y`. A family can map
many inputs to the same result. When the only occurrence of `P` is inside
a family application, pass `P` explicitly.

On a recursive call the new input must be a proper structural part of the
earlier input to the same family. `Dual(K)` meets that rule because `K` is
a type argument of the current `Send` or `Recv`. Returning to the same
family through another family is subject to the same check.

The evaluator allows 128 nested family calls and 4,096 structural steps
per outer reduction. It also bounds the expanded result at 4,096 type
nodes, checking both type arguments and inline fields. Exceeding a bound
produces a compile error at the reduction.

The resulting type determines layout, ownership and calling convention.
For example, a family reducing to `String` produces an owning string, and
one reducing to `[u8; 2]` produces an ordinary two-byte array. Equation
selection finishes before code generation. This feature is available in
ordinary modules on both Jihoo targets.
