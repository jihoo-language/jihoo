# Observer-indexed history types

How many observations does it take to tell two resource histories apart?
The experimental type operator `history.Separation(H, K, S)` computes
the shortest ordered record length for slot `S` that distinguishes the
histories. A related operator, `history.Observe(H, S)`, gives the final
observation a type that can index an ordinary struct, including one that
owns data.

## A difference that takes three observations

Suppose two controllers visit the following states and then stop.

| Controller | Changes visible on its status slot |
| --- | --- |
| A | red, blue, red, blue, done |
| B | blue, red, blue, red, done |

The final reading is free. A recorded sample contains the state alone,
without a clock, event number or indication that it was the first change.
A recorder can skip changes and preserves the order of the samples it keeps.
The controllers admit the same one-sample records and the same two-sample
records, including two reds or two blues. The record **red, red, blue** can
come only from A.
The compiler therefore computes `history.Apart(3)`. Some three-sample
records, such as **red, blue, red**, are still possible in both.
[Runnable observation-budget example](../../examples/observation_budget.jh)

The result is a type that other code can inspect. For example, a closed
type family can turn the minimum record length into an array length.

```jihoo
import std.history as h

type Record {
    h.Apart(let N) => [u8; N]
    h.Indistinguishable => ()
}
```

An API can require the result to be `h.Apart(3)` in a signature.
If a change makes the two histories distinguishable at the end,
the result becomes `h.Apart(0)` and the signature fails to check.

## The draft and the inbox

```jihoo
import std.history as h

struct Source {}
struct Draft {}
struct Inbox {}
struct Compose {}
struct Send {}
struct Reset {}

type Prepare = h.Put(Draft, Compose, h.Read(Source))
type Publish = h.Put(Inbox, Send, h.Read(Draft))
type Clear = h.Put(Draft, Reset, ())

type SendFirst = (Prepare, Publish, Clear)
type ClearFirst = (Prepare, Clear, Publish)

struct Packet(V: type) { body: String }

fn accept(sink p: Packet(h.Observe(SendFirst, Draft))) -> Packet(h.Observe(ClearFirst, Draft)) {
    p
}
```

Both calls to `Observe` in `accept` compute the same type, so the function
can return the original packet by moving it. Substitute `Inbox` for both
occurrences of `Draft` and the return fails type checking. Here are the
symbolic values that account for the difference.

| Observed slot | Send before clearing | Clear before sending |
| --- | --- | --- |
| `Draft` | `Reset()` | `Reset()` |
| `Inbox` | `Send(Compose(initial(Source)))` | `Send(Reset())` |

The `Send` operation is the same in both schedules. Its input names the
version of `Draft` available at the time of the send. A later write to
`Draft` leaves that earlier input intact. The runnable example passes an
owned value between APIs using the computed type. [Example](../../examples/observed_histories.jh)

## Formation and evaluation

A slot identifies a resource, and a label identifies an operation. Declare
them as ordinary structs or enums. Type aliases preserve their identities.
Each slot starts live with its own symbolic input. A history is `()`, a
single `Put`, or an ordered tuple of histories. Thus `(P, Q)` runs `Q`
in the state left by `P`. Parenthesizing subsequences preserves the order.

- `h.Put(D, L, ())` writes a symbolic expression labeled `L` in
  slot `D`. Its value has no input dependencies.
- `h.Put(D, L, h.Read(S))` takes the current value of `S` as the input
  to `L`. Both slots are live after the write.
- `h.Put(D, L, h.Take(S))` also samples that input and marks `S` spent.
  The write to `D` happens last. When `D` is `S`, this is a valid
  consume-and-replace operation.
- A tuple of inputs supplies arguments in order. Reading the same slot
  twice is valid. Taking a slot requires it to be the only occurrence of
  that slot in the update's inputs. Every input must be live. A later write
  can reinitialize a spent slot.

For a precise equality judgment, let a symbolic value be either
`initial(s)` or `made(label, v₁, …, vₙ)`. A world maps each slot to a
live symbolic value or to `spent`. Evaluate each update by looking up all
its inputs in the incoming world, marking its taken slots spent, and
installing the new symbolic value. An invalid lookup rejects the entire
history, even when the eventual observer selects a different slot.

```text
world(H)        = state reached by evaluating H from the initial world
normal(H, s)    = (s, world(H)[s])
H ≡ₛ K          iff both histories are valid and normal(H, s) = normal(K, s)
```

Equality on the right is structural. Labels and initial slots have nominal
type identity, argument order matters, and a spent slot is distinguishable
from a live slot. Identical labels applied to identical input versions
give identical symbolic values. To distinguish individual acquisitions,
give them distinct labels or inputs.

## Equality with a recording budget

During evaluation, write down the initial state of the observed slot and
its state after every update. Collapse consecutive equal states, including
steps that only touch other slots. Call the resulting sequence `trace(H, s)`.
For a budget `k`, its possible records are all subsequences of length at
most `k`. Samples can be separated by any number of skipped changes.

```text
H ≡ₛ,ₖ K   iff   H ≡ₛ K and their sets of possible records of length ≤ k agree
```

Increasing the budget can only distinguish more histories. If the final
states differ, their separation is zero. Otherwise the least budget that
distinguishes the histories is the length of the shortest subsequence of
either trace absent from the other. Equal traces give `h.Indistinguishable`.
An invalid resource access is a type error at every budget.

This gives a law for comparing three valid histories at the same slot.
Write `sep(H, K)` for their separation and give equal traces the value
`∞`. Then

```text
sep(H, K) ≥ min(sep(H, M), sep(M, K))
```

For every budget below the minimum, the final reading and possible records
of `H` agree with those of `M`, which in turn agree with those of `K`.
So no record at that budget can distinguish `H` from `K`. For instance,
if each of two successive revisions preserves all two-sample observations,
the first and last revisions preserve them too.

One way to compute the minimum is to consider a value in the first
trace. A candidate record may skip it, or keep it and match its earliest
available occurrence in the second trace. If that occurrence is absent,
the single value already distinguishes these suffixes. Otherwise continue
after the match. Taking the smaller successful length, then doing the
same calculation in the other direction, gives the minimum. Each pair of
suffix positions needs one comparison per direction.

The evaluator allows 4,096 sequence-node visits per history, counting
tuple structure, updates and their operands. Equal compressed traces and
different final states are recognized directly. For other pairs,
`Separation` compares up to 1,048,576 pairs of trace positions. Exceeding
a bound produces a compile error.

## What composes

Two independent writes may exchange places. A sufficient condition is
that neither step writes or takes any slot the other step reads, takes or
writes. Both orders then leave every observer with the same symbolic
value and availability. Steps may share read-only inputs.

Equality for a single observer allows more schedules to agree. It applies
to the observation type itself. If a later step copies `Inbox` back into
`Draft`, it can distinguish the two schedules in the table even at
`Draft`. To compare longer schedules, append that step to both histories
and observe again.

The judgment describes events explicitly written in types. Programmers
choose the meaning of each label and implement the runtime operations it
stands for. Jihoo performs the symbolic comparison while checking types.
The ordinary move and borrow rules continue to apply to values such as
the packet in `accept`.

## Design context

Cubical type theory gives an identity computational structure through
paths, squares and higher-dimensional cubes. The design question adapted
here is what an equality computes in a systems language. This experiment
answers it for finite, labeled histories and selected resources.
[Cohen, Coquand, Huber and Mörtberg](https://arxiv.org/abs/1611.02108)

Tracking the inputs from which a result was derived has a history in
provenance research. The rules above combine ordered provenance and
resource consumption in a type-conversion judgment.
[Cheney, Acar and Ahmed](https://arxiv.org/abs/0812.0564)

On a pair of already projected traces, agreement on all subsequences up
to length `k` is Simon's congruence. Jihoo chooses the alphabet from live
provenance and spent states, collapses unobservable steps, supplies the
final state for free, and returns the distinguishing budget as a type.
[Efficiently Testing Simon's Congruence](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2021.34)
