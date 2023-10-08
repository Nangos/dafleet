# DafLeet: Verifying Leetcode Problems in Dafny

Just a project for fun...

## Logistics

So far, Dafny is the program verification tool of the "most fun" in my personal opinion.
It is very intuitive to use, expressive enough, and fun to interact with (especially in vs-code).

For now (Year 2023), though, Dafny is still not mature enough for ideal end-to-end verification,
meaning it's still an annoyingly tough task to *emulate* a real program with 100% fidelity and then perfectly verify it.

Therefore, instead of e.g. writing a full library containing types like `MutableList<T>` or `MutableDict<K, V>`, I will simply stick to Dafny's built-in types like `seq<T>` or `map<K, V>`. While the **former** is "more real", I had to insert much meaningless *boilerplate* during the verification when I tried it.

So I decided to use the **latter** style and just *pretend*. For example, when I **write** `m := m[k := v]` which ~~seems to construct a new object~~, what I really **mean** is the in-place constant operation `m[k] := v` for updating a (hash) map. I will just *assume* such equivalences in mind, without verifying.

By doing so, I will just focus on the "fruit" of each problem, and abandon any secondary details that *unnecessarily challenges* the current Dafny.

## What to expect from this repo

For each problem, I will give a *basic* solution for it, **verified**. I will write detailed comments, where I elaborate my strategy for both solving and verifying the problem. Typically there will also be a *discussion* section where I share what I've learned from the verification process, and perhaps keep on verifying "better-than-basic" solutions if applicable.

All these comments are meant to let you read! (Of course, *I assume you are also a fan of Dafny; at least you know the syntax.* In other words, this repo will be more like a **blog** than a ~~tutorial~~.)

## Heads up...

Nothing much for now.