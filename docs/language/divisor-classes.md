# Graph divisor types

Three credits at vertex A of a triangle can be exchanged for three credits
at B. One credit at A cannot be exchanged for one at B. A vertex may
trade one credit per incident edge for one credit at the other end of
each edge. The trade is reversible.

On the triangle, two credits at A buy one at B and one at C. From three at
A, keep one and make that trade. Now use the credits at A and C to buy two
at B. There were three credits throughout.

```text
3A  ↔  A + B + C  ↔  3B
```

To see why fewer copies fail, assign weights 0, 1 and 2 to A, B and C.
Every permitted trade preserves the weighted sum modulo three. One credit
at B has weight 1, two have weight 2, and any number at A has weight 0.
Three is the first positive number for which the obstruction disappears.

## Using a class in a function signature

The experimental `std.divisor` module gives a placement of signed credits,
called a *divisor*, a type representing its equivalence class. Vertices
are numbered from zero. Here A, B and C are 0, 1 and 2.

```jihoo
import std.divisor as d

type Triangle = d.Graph(3, (d.Edge(0, 1), d.Edge(1, 2), d.Edge(2, 0)))
type ThreeAtA = d.Class(Triangle, d.At(0, 3))
type ThreeAtB = d.Class(Triangle, d.At(1, 3))

struct Lot(C: type) { payload: String }

fn relabel(sink lot: Lot(ThreeAtA)) -> Lot(ThreeAtB) { lot }

fn period(value: d.Order(Triangle, d.At(0, 1), d.At(1, 1))) -> d.Period(3) {
    value
}
```

`relabel` returns the original owned value. Changing both class aliases
to a single credit makes that return a type error. The ordinary move
checker also rejects using a moved lot a second time.
The runnable example uses the computed period as an array length.
[Divisor class example](../../examples/divisor_classes.jh)

A class can also serve as a slot in `std.history`. Suppose one history
writes a label to `ThreeAtA` and another writes the same label to
`ThreeAtB`, each with empty inputs. An observer at `ThreeAtA` sees
identical traces because both writes target the same slot. With a single
credit at each vertex, the second write targets a different slot. Their
final readings already differ, so the separation at A is `Apart(0)`.
[Observer-indexed history types](observed-histories.md)

## Graphs and their periods

`d.Graph(N, Edges)` describes a finite undirected graph. `Edges` can be
`()`, a single `d.Edge(a, b)`, or a nested tuple of edges. `Class` and
`Order` interpret these descriptions. Reversing an edge and reordering
or regrouping the tuple give the same computed results. Repeating an edge
adds a parallel edge. Isolated vertices are included in `N`. Class
identity includes vertex labels and edge multiplicities.

A divisor can be `()`, a single `d.At(vertex, amount)`, or a nested tuple
whose entries are added. Amounts are signed 64-bit integers. A negative
coefficient describes a debt. The equivalence permits integer combinations
of the local trades. An application that requires a nonnegative balance
after every runtime step must track that condition separately.

`d.Order(G, D, E)` returns `d.Period(k)` for the smallest positive `k`
for which `kD` and `kE` are equivalent. Exactly the positive multiples of
`k` work. A batch that already contains `m` copies has period
`k / gcd(k, m)` for positive `m`. Equivalent divisors have period one.
If a connected component would have to gain or lose credits in total,
the result is `d.Unbalanced`.

| Graph | Placement of a single credit | Result |
| --- | --- | --- |
| Three-vertex path | One end to the other | `Period(1)` |
| Triangle | One vertex to a neighbor | `Period(3)` |
| Square cycle | One vertex to its opposite | `Period(2)` |
| Square cycle | One vertex to a neighbor | `Period(4)` |
| Two isolated vertices | One vertex to the other | `Unbalanced` |

## Why the calculation works

Write `L` for the graph Laplacian. Its diagonal gives vertex degrees and
its off-diagonal entries are the negatives of the edge multiplicities.
The columns are the changes made by the reversible trades, up to sign.
Thus two divisor vectors `D` and `E` represent the same class exactly when
`D − E = Lf` for an integer vector `f`. In each connected component
this requires equal total degree.

Ground one vertex in each component by setting its coordinate in `f` to
zero. After removing its row and column, the reduced Laplacian `M` is
invertible. Write `τ = det(M)`. By Cramer's rule each remaining coordinate
of the rational solution for a divisor difference is a numerator divided
by `τ`. It becomes integral precisely when its denominator in lowest terms
divides the number of copies. The least common multiple of these
denominators, across all components, is the period. To index one divisor,
the compiler takes its non-root coefficients as the right-hand side. The
graph, the component totals and these numerators modulo `τ` determine its
class. An isolated vertex contributes only its total.

This is the linear equivalence of divisors on graphs. Its degree-zero
classes on a connected graph form the graph Jacobian. Jihoo uses these
classes for type conversion and exposes the order of a difference as a
type. The experiment accepts loopless graphs with one to eight vertices
and up to 32 edges, counting parallel edges individually. Evaluation visits
at most 4,096 tuple and entry nodes per edge or divisor expression.
[Baker and Norine, *Riemann–Roch and Abel–Jacobi theory on a finite graph*](https://arxiv.org/abs/math/0608360)
