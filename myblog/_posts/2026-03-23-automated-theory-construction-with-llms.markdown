---
layout: post
title: "Growing Theories with LLMs and Lean"
date: 2026-03-23 09:00:00 +0900
categories: research lean llm
---

About six years ago, when I was in high school, I often felt overwhelmed by the rows of advanced mathematics books in large bookstores. At the same time, I was fascinated by the fact that such rich theories could emerge from relatively small sets of axioms.

Since then, I have been interested in the idea of generating mathematical structure automatically from simple foundations. Traditional automated theorem proving has been powerful for proving individual statements, but it has been less effective as a tool for exploring and extending theories at a higher level.

Recently, the mathematical abilities of large language models have improved substantially. They can assist with proofs, suggest reformulations, and sometimes propose useful follow-up questions. Motivated by this, I started the [`automated-theory-construction-lean4`](https://github.com/tukamilano/Automated_Theory_Construction) repository to explore how LLMs can complement formal verification and help with theory construction itself.

## Overview

The basic idea is simple: start from a small axiom system, introduce a few seed propositions, and then repeatedly try to formalize, verify, and extend the resulting theory.

Each iteration looks roughly like this:

1. Put a base axiom system and a collection of elementary seed propositions into an open problem queue.
2. Retrieve one proposition from the queue and ask Codex CLI to formalize either a proof or a counterexample within a fixed time budget.
3. If the proposition is successfully formalized and verified, add it to `Derived.lean` as a theorem.
4. Use the logs produced during the attempt to decide what to do next:
   if the proposition was not formalized, put it back into the queue together with its subgoals;
   if it was formalized, generate more general candidate problems and add them to the queue.

In this way, the system alternates between proving statements and proposing new directions for exploration.

The most important part is the prompt used to generate follow-up problems after a successful result:

```text
When the current problem is solved and verified (`verify_success = true` and `result = proof|counterexample`):
- Prefer outward-looking follow-up problems that extend the theory rather than merely staying near the last proof script.
- Favor, in roughly this order:
  1. natural generalizations or reusable abstractions
  2. converses, strict separations, or failure-of-converse statements
  3. existence, uniqueness, impossibility, or rigidity phenomena
  4. finite-model behavior, extremal behavior, boundary cases, or classification fragments
  5. adjacent structural consequences that clarify the global shape of the theory
- It is good to return at least one candidate that meaningfully broadens, reinterprets, or reuses the verified result beyond the immediate local target.
- Prefer candidates whose resolution would teach something non-obvious about the theory or its models, rather than merely restating the solved fact in slightly altered form.
- If a more informative model-level, structural, or boundary-case follow-up is available, prefer it over a nearby local rewrite.
```

The goal is not merely to stay close to the last proof, but to push outward toward statements that clarify the structure of the theory.

## How It Works

The core loop lives in `scripts/run_loop.py`. At the moment, the implementation uses fixed paths:

- theory: `AutomatedTheoryConstruction/Theory.lean`
- accumulated theorems: `AutomatedTheoryConstruction/Derived.lean`
- temporary verification file: `AutomatedTheoryConstruction/Scratch.lean`
- initial seeds: `AutomatedTheoryConstruction/seeds.jsonl`
- runtime state: `data/`

So this is not yet a fully generic multi-theory runner. Switching to a different theory currently requires editing these files directly.

Each iteration proceeds as follows:

1. Select the next open problem deterministically.
2. If the problem is not already in Lean form, use `prover_statement` to translate it into a formal statement.
3. Use `prover` to attempt a proof, a counterexample, or determine that the problem is currently stuck.
4. Run `formalize`, then verify the result with:

`lake env lean AutomatedTheoryConstruction/Scratch.lean`

5. If verification fails, invoke `repair` repeatedly until the retry budget is exhausted.
6. If verification succeeds, append the resulting theorem to `Derived.lean`.
7. Run `expand` to generate additional candidate problems.
8. Update the system state deterministically (`open`, `solved`, `counterexamples`).

Open problems may be either Lean-formal statements or semi-formal natural language prompts. Problems that cannot yet be formalized remain in the queue.

## Three-Stage Formalization

Proof formalization is split into three stages:

1. formalization of the statement
2. natural language proof generation
3. formalization of the proof in Lean

This decomposition helps separate semantic understanding from syntactic verification.

## Current Experiment

At the moment, I am experimenting with code adapted from [SnO2WMaN/provability-toy](https://github.com/SnO2WMaN/provability-toy), which I incorporated into `Theory.lean`. I also added the following four propositions to `seeds.jsonl`:

```lean
∀ {α : Type u} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ g : ACR.GödelFixpoint α, g.1 ≤ □g.1
∀ {α : Type u} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, g.1 ≡ h.1
∀ {α : Type u} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ⊠(⊤ : α) ≡ ⊠⊠(⊤ : α)
∀ {α : Type u} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ∃ g : ACR.GödelFixpoint α, g.1 ≡ ⊠(⊤ : α)
```

These are formalized versions of statements from Sections 2 and 3 of [arXiv:1602.05728v1](https://arxiv.org/abs/1602.05728v1).

The results obtained so far are available in [this gist](https://gist.github.com/tukamilano/d25609aeb416005e24be23308c4abd3d). I am currently receiving feedback on the generated code.

I attach the [ChatGPT response](https://chatgpt.com/share/69c0ea0a-8d40-8008-bc0b-892de6a6b429) for reference.

## What I Still Do Not Fully Understand

I am not a specialist in provability logic, so there are still parts of the underlying mathematics that I do not fully understand. For now, I see this project primarily as an experiment in how LLMs and Lean can be combined to support theory exploration.

I plan to study this area more carefully and write a more detailed explanation later. If you work in provability logic or related areas, I would be very happy to hear your thoughts.

## Goals

One major goal is to enable the system to incorporate more general propositions into the theory as theorems, especially statements that are less tightly tied to a specific internal language.

Ideally, I would also like the resulting theories to acquire a consistent style and structure, closer to files such as `Basic.lean` in mathlib.

In logic, language theory, and type theory, it is common to come up with small axiom systems whose importance is not immediately clear. As a result, they tend to be deprioritized. I hope this project can serve as a tool for exploring what kinds of theories emerge from such systems and for deciding which ones are worth developing further.

I plan to keep improving the system as AI tools continue to advance. If you have small axiom systems you would like to experiment with, feel free to let me know.

## Acknowledgments

I am grateful to SnO2WMaN for publishing `provability-toy`.
