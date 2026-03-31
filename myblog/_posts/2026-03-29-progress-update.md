---
layout: post
title: "Progress Update"
date: 2026-03-29 21:00:00 +0900
categories: notes progress draft
---

layout: post
title: "Progress Update"
date: 2026-03-29 21:00:00 +0900
categories: notes progress draft
--------------------------------

The implementation of the features I had planned is now largely complete. Going forward, I will continue making incremental improvements, while shifting the main focus toward exploring how this system can be applied in broader contexts.

Improving the system to discover and verify more complex proofs would require a substantial increase in inference resources. Given this constraint, I plan to prioritize expanding its range of applications rather than pushing purely on raw proof complexity for now.

## Parallelization

To improve throughput and avoid bottlenecks from slow sessions, I introduced a parallel execution scheme:

* Problems are taken from `open_problems` and processed through the pipeline
  *(formalization of the statement → natural language proof → formal proof → expansion)*
  with up to *n* problems running concurrently.
* The system does not wait for slower sessions; it proceeds with other available problems.
* The `main_theorem_session` runs in parallel as a dedicated single slot, separate from the *n* slots for `open_problems`.

This allows the system to maintain steady progress without being blocked by particularly difficult instances.

## Expanding Applications

Originally, this repository aimed to construct theories in unexplored domains. However, this raises a natural question:
*what is the value of building theories in areas that humans themselves do not yet understand?*

Rather than viewing this as a limitation, I now interpret it more positively. The system can be seen as a tool that expands a researcher's imagination when they conceive a new, unexplored theme.

In this sense, the goal is not merely to target niche or underexplored fields, but to support the early-stage development of entirely new research directions.

As a concrete step in this direction, I am interested in collaborating with researchers working on:

* a comprehensive analysis of the expressive power of individual rules in combinatory categorial grammar, and
* a structural understanding of the landscape surrounding mildly context-sensitive grammars.

I believe this system has the potential to accelerate such investigations by systematically generating and organizing candidate statements and their formal properties.

## Outlook

I will continue exploring new application domains where this framework can contribute meaningfully, while refining the system to better support theory construction workflows.
