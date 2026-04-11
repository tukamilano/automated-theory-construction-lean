# **Structural Foundations and Research Trajectories in the Lambek Calculus: Toward a Unified Theory of Substructural Grammars**

## **Table of Contents**

1. [The Substructural Landscape and the Hierarchy of Logics](#1-the-substructural-landscape-and-the-hierarchy-of-logics)
2. [Structural Correspondences and Language Hierarchies](#2-structural-correspondences-and-language-hierarchies)
3. [Extraction of Logical Rules and Complexity Characterizations](#3-extraction-of-logical-rules-and-complexity-characterizations)
4. [Provability Relations and Rule Reducibility](#4-provability-relations-and-rule-reducibility)
5. [Discovery of Invertibility and Focusing Strategies](#5-discovery-of-invertibility-and-focusing-strategies)
6. [Separability of Logical Systems](#6-separability-of-logical-systems)
7. [Completeness and Algebraic Reasons for Model Limits](#7-completeness-and-algebraic-reasons-for-model-limits)
8. [The Boundary Between Cut Elimination and Decidability](#8-the-boundary-between-cut-elimination-and-decidability)
9. [The Syntax-Semantics Interface and Curry-Howard](#9-the-syntax-semantics-interface-and-curry-howard)
10. [Canonical Objectives and Future Directions](#10-canonical-objectives-and-future-directions)
11. [Conclusion: Synthesizing the Structural Theory](#11-conclusion-synthesizing-the-structural-theory)
12. [Works Cited](#works-cited)

The development of the Lambek calculus since its introduction in the late 1950s represents one of the most significant convergences of proof theory, algebraic logic, and mathematical linguistics. Originally conceived by Joachim Lambek as a "syntactic calculus" for the mathematical description of natural language, the system has evolved into a foundational framework for the study of substructural logics.1 These logics are characterized by the systematic restriction or removal of the structural rules—Exchange, Weakening, and Contraction—that are taken as axioms in classical and intuitionistic systems.1 By focusing on the order and multiplicity of premises, the Lambek calculus and its extensions provide a rigorous mechanism for modeling resource-sensitive phenomena, ranging from the linear precedence of words in a sentence to the execution of linear programs in computer science.1  
This research report delineates the structural theory of the Lambek calculus, moving beyond the cataloging of isolated linguistic examples toward a systematic investigation of logical-language correspondences. It evaluates the provability relations among structural rules, the discovery of invertibility in proof search, the rigorous separation of expressive power between systems, and the algebraic limits of completeness theorems. Furthermore, it identifies the sharp boundaries of decidability and cut-elimination in the presence of restricted structural rules and explores the structural preservation properties inherent in the mapping from syntactic types to semantic representations via the Curry-Howard correspondence.5

## **1. The Substructural Landscape and the Hierarchy of Logics**

The taxonomy of substructural logics is defined by the absence of one or more structural rules present in classical logic.1 While classical logic assumes that the order of assumptions is irrelevant (Exchange), that any assumption can be used multiple times (Contraction), and that irrelevant assumptions can be introduced without affecting validity (Weakening), substructural logics treat assumptions as finite resources.7 The three primary lines of inquiry—philosophy (relevant logics), linguistics (the Lambek calculus), and mathematics (linear logic)—were unified in the 1990s into a coherent landscape where the Lambek calculus occupies a central position as the most structure-sensitive member of the hierarchy.1  
At the base of this hierarchy lies the non-associative Lambek calculus (NL), which Lambek introduced in 1961 as a refinement of his earlier 1958 system.9 While the 1958 calculus (L) was sensitive to the order of assumptions, it assumed that the grouping of those assumptions was irrelevant (Associativity). NL, by contrast, is sensitive to both order and grouping, making it a logic of hierarchically structured trees rather than simple strings.5 Adding structural postulates to NL generates a variety of systems with increasing flexibility.

### **Table 1: Structural Postulates and Logical Systems in the Lambek Hierarchy**

| System | Structural Postulate | Form of Postulate | Sensitivity | Target Structure |
| :---- | :---- | :---- | :---- | :---- |
| **NL** | None | N/A | Order and Grouping | Hierarchical Trees |
| **L** | Associativity (ASS) | [formula omitted in source conversion] | Order Only | Linear Strings |
| **NLP** | Commutativity (COM) | [formula omitted in source conversion] | Grouping Only | Multisets of Trees |
| **LP** | ASS \+ COM | Both | Multiplicity Only | Multisets of Formulas |
| **ILL** | ASS \+ COM \+ WEAK \+ CONT | All | Classical | Standard Formulas |

The logic LP, often referred to as the Lambek-van Benthem calculus, represents the intuitionistic multiplicative fragment of linear logic.7 It was introduced by van Benthem in 1986 to provide a natural relation with a fragment of the lambda calculus, but it also provides a logical basis for modeling languages with free word order.5 The movement across this landscape is characterized by the decomposition of connectives; structural rules destroy the organization of type assumptions, leading to the collapse of connectives that can be distinguished in more structured logics.7 For instance, the two directed implications (slashes) of L collapse into a single undirected implication in LP because the order-sensitivity that necessitates the distinction is removed by the exchange rule.5

## **2. Structural Correspondences and Language Hierarchies**

A primary objective of the structural theory is the discovery of logical systems that correspond to meaningful classes within formal language hierarchies.11 The most famous such correspondence is the proof of the Chomsky conjecture by Pentus, which established that Lambek grammars based on L generate exactly the class of context-free languages (CFL).2 This result demonstrates that the removal of exchange and contraction from intuitionistic logic leaves a system that is precisely powerful enough to recognize the recursive structures of context-free grammars.12  
However, natural language syntax frequently exhibits non-context-free phenomena, such as cross-serial dependencies in Swiss German or Dutch, which require greater expressive power.2 This necessitates the exploration of extensions that sit between L and LP or generalize the calculus to first-order systems. One such "umbrella" logic is the first-order multiplicative intuitionistic linear logic (MILL1).11 The Lambek calculus can be embedded into MILL1 by using variables to "fix" the order of formulas, but MILL1 grammars are significantly more powerful.11

### **Table 2: Correspondences Between Logical Systems and Language Classes**

| Logical System | Structural Constraints | Language Class | Complexity |
| :---- | :---- | :---- | :---- |
| **L** | Associative, Non-commutative | Context-Free (CFL) | NP-Complete |
| **NL** | Non-associative | Non-associative CFL | PTIME |
| **LP** | Associative, Commutative | Permutation closures of CFL | NP-Complete |
| **MILL1** | First-order Multiplicative | Hypergraph Languages | NP-Complete |
| **L \+ Intersection** | Additive Conjunction | Context-Free [formula omitted in source conversion] CF | PSPACE-Complete |

Research into MILL1 grammars has shown that they can generate non-semilinear languages and even NP-complete languages, illustrating a jump in power that occurs when the structural sensitivity of L is generalized to first-order structures.11 This highlights a critical theme in the research agenda: identifying the specific logical rules that characterize these higher-level language classes while maintaining a rigorous characterization of the accompanying computational complexity.11

## **3. Extraction of Logical Rules and Complexity Characterizations**

The computational complexity of the Lambek calculus and its variants is a central concern of the structural theory. While the non-associative Lambek calculus (NL) is decidable in polynomial time (PTIME), the addition of associativity in L pushes the complexity to NP-completeness.2 This NP-completeness holds even for the product-free fragments of L, such as those containing only the slashes [formula omitted in source conversion].2 The only polynomially decidable fragment of L is the one containing only a single implication (e.g., only ), a result established by Savateev in 2007\.2  
The complexity profile of these systems is further complicated by the addition of additive connectives—conjunction ([formula omitted in source conversion]) and disjunction ([formula omitted in source conversion]). While NL is in PTIME, the addition of classical (non-distributive) conjunction and disjunction makes the system undecidable.15 If the additive connectives are distributive, the logic (DFNL) becomes decidable in exponential time (EXPTIME).15 This demonstrates that the interaction between structural rules and the lattice structure of connectives is a primary driver of computational difficulty.

### **Table 3: Complexity of Derived Lambek Fragments and Extensions**

| Calculus Fragment | Additional Rules/Connectives | Complexity | Key Researcher |
| :---- | :---- | :---- | :---- |
| **NL** | None | PTIME | Buszkowski (1987) |
| **L** | Associativity | NP-Complete | Pentus (2006) |
| **L (, /)** | Slashes only | NP-Complete | Savateev (2008) |
| **L ()** | Single implication | PTIME | Savateev (2007) |
| **L \+ [formula omitted in source conversion]** | Additive Conjunction | PSPACE-Complete | Kuznetsov (2020) |
| **FLec** | Contraction (Commutative) | Decidable (Hyper-Ackermannian) | Ramanayake (2020) |
| **FLew** | Weakening (Commutative) | Decidable (Hyper-Ackermannian) | Balasubramanian (2020) |

A particularly notable result in recent years is the characterization of extensions of the commutative Full Lambek calculus (FL) with contraction (FLec) or weakening (FLew).16 These logics, which admit hypersequent calculi, have been shown to be decidable, but they entail a jump from Ackermannian to hyper-Ackermannian complexity in the fast-growing hierarchy.16 This suggests that the presence of even restricted forms of contraction or weakening introduces a level of computational demand that far exceeds the base Lambek systems.16

## **4. Provability Relations and Rule Reducibility**

A core target of the structural theory is the determination of whether one structural rule can realize a transformation equivalent to another by combining other rules or modalities.19 This is often explored through the introduction of asymmetric exchange rules whose effect depends on operator directionality.19 For example, a system might allow [formula omitted in source conversion] to be transformed into [formula omitted in source conversion], but forbid the transformation to [formula omitted in source conversion]. Such rules allow for fine-grained control over the "travel" of hypotheses within a sequent, a feature that is essential for modeling "scrambling" in languages like German or Japanese without collapsing into full commutativity.19  
Research into the "Graded Lambek Calculus" has proposed that the prover or programmer should be able to declare when and in what direction hypotheses are allowed to be exchanged.19 This is achieved by enriching the logic with subexponentials—unary modalities that license the local application of structural rules.9 These modalities provide controlled access to stronger structural rules from within weaker ones.7  
Reducibility is also examined through the use of monoidal adjoint functors that connect different structural regimes.22 For example, a mixed commutative/non-commutative logic (CNC logic) can be formulated where an exchange modality is derivable using the adjunction between an intuitionistic linear logic (which allows exchange) and the Lambek calculus (which does not).22 This allows the "pulling" of the exchange structural rule from one side of the logic to the other, creating a principled bridge between ordered and unordered resource management.22

## **5. Discovery of Invertibility and Focusing Strategies**

Invertibility identifies rules or systems such that the premises can be derived from the conclusion, allowing for a deterministic proof search.23 In the context of the Lambek calculus and its semi-substructural extensions, identifying invertible rules is crucial for developing focused sequent calculi.23 These calculi organize the proof search into phases: an "invertible" (asynchronous) phase where rules are applied greedily, and a "non-invertible" (synchronous) phase where a specific formula is focused upon.23

### **Table 4: Invertibility in Focused Lambek-style Calculi**

| Connective | Rule Type | Phase | Invertibility Status |
| :---- | :---- | :---- | :---- |
| **[formula omitted in source conversion] (Additive)** | **[formula omitted in source conversion]** | Right Invertible | Invertible |
| [formula omitted in source conversion] **(Linear Implication)** | **[formula omitted in source conversion]** | Right Invertible | Invertible |
| [formula omitted in source conversion] **(Multiplicative)** | **[formula omitted in source conversion]** | Right Non-Invertible | Non-Invertible |
| [formula omitted in source conversion] **(Additive)** | **[formula omitted in source conversion]** | Left Non-Invertible | Non-Invertible |
| [formula omitted in source conversion] **(Additive)** | **[formula omitted in source conversion]** | Right Non-Invertible | Non-Invertible |

Focusing strategies help solve the problem of "spurious ambiguity," where multiple distinct proofs correspond to the same semantic analysis.23 By employing tag annotations (e.g., P, C1, C2, R), researchers can manage the non-deterministic choices in bottom-up proof search, ensuring that distinct proofs in the calculus correspond to canonical representatives of an equivalence relation.23 These strategies have been formalized in proof assistants like Agda to guarantee the correctness of the focused calculi.23 This normalization is potentially scalable to the full Lambek calculus and its extensions, providing a tool for rigorous structural analysis.23

## **6. Separability of Logical Systems**

Separability involves finding propositions that are provable in one logical system (set A of structural rules) but not in another (set B), thereby establishing a formal separation of their expressive power.4 This is critical for distinguishing the subtle differences between associative and non-associative systems, or between commutative and non-commutative ones.4  
For instance, the Geach law [formula omitted in source conversion] is a theorem in the associative Lambek calculus (L) but not in the non-associative version (NL), unless specific bracketings are assumed.10 This separation illustrates that L is capable of functional composition in a way that NL is not.10 Similarly, the "lifting" or "type raising" rule [formula omitted in source conversion] is a theorem in L but not in the original Ajdukiewicz-Bar-Hillel calculus, which lacked the right-introduction rules for slashes.5  
Separability results are also used to analyze the impact of additive connectives. The product-free Lambek calculus enriched with conjunction only (L\<) is complete with respect to language models, but the addition of disjunction (LV) leads to incompleteness because of the distributive law.27 This separation between L\< and LV highlights the structural consequences of lattice-theoretic properties in the substructural setting.27

## **7. Completeness and Algebraic Reasons for Model Limits**

A deeper understanding of completeness for the Lambek calculus involves clarifying the limits of theorems with respect to specific model classes, such as finite models or language models (L-models).2 L-models are inspired by the intended linguistic application, where types are interpreted as sets of strings and product as concatenation.13 While the product-free fragment of L is L-complete, the full calculus with product presented challenges until Pentus proved its L-completeness in 1995\.2  
However, adding additives ruins this completeness. The product-free Lambek calculus with disjunction is incomplete with respect to both L-models and relational models (R-models).27 R-models interpret types as binary relations on a set, with the product corresponding to relation composition.14 The strong completeness of L with respect to R-models over transitive binary relations was established by Andréka and Mikulás.14

### **Table 5: Completeness and Incompleteness in the Lambek Calculus**

| System | Model Class | Status | Algebraic Reason |
| :---- | :---- | :---- | :---- |
| **L (Product-free)** | L-Models | Complete | Buszkowski (1982) |
| **L (Full)** | L-Models | Complete | Pentus (1995) |
| **L with [formula omitted in source conversion]** | L-Models | Complete | Buszkowski |
| **L with [formula omitted in source conversion]** | L-Models / R-Models | Incomplete | Distributive Law Gap |
| **L with [formula omitted in source conversion]** | L-Models / R-Models | Incomplete | Distributivity |
| **L (Product-free)** | Relational Models | Strongly Complete | Andréka/Mikulás (1994) |

The structural reasons for these limits often lie in the algebraic properties of the models versus the logic. For example, L-models and R-models inherently satisfy the distributive law for additives (conjunction over disjunction), but the Lambek calculus does not.15 Thus, any sequent that is true in all distributive models but not derivable in the logic represents a point of incompleteness.27 Furthermore, the finite model property (FMP) has been established for fragments like BCI and certain restricted versions of the Lambek calculus using the "method of barriers," but many extensions do not enjoy this property, complicating their decidability.29

## **8. The Boundary Between Cut Elimination and Decidability**

The cut-elimination theorem is a hallmark of well-behaved logical systems, ensuring that any provable theorem can be derived without using the Cut rule, which in turn provides the subformula property and a basis for decidability.7 A canonical target of the structural theory is identifying the sharp boundary at which decidability is lost when structural rules are introduced.15  
In the case of the non-associative Lambek calculus (NL), the finitary consequence relation is decidable in PTIME.15 However, adding classical (non-distributive) lattice connectives (FNL) makes the consequence relation undecidable.15 This is a critical result: it shows that even in a system without exchange, the interaction of additives can lead to undecidability.15 Interestingly, if the additives are distributive (DFNL), decidability is regained, though with higher complexity.15  
The boundary is even more delicate in commutative systems. Extensions of the commutative Full Lambek calculus (FL) that admit cut-free hypersequent calculi have been shown to be decidable.17 However, this decidability comes with hyper-Ackermannian upper bounds for systems with contraction or weakening.16 This suggests that cut-elimination and decidability can be maintained in the presence of these rules, but only through the use of more sophisticated proof-theoretic structures like hypersequents, and at the cost of extreme computational complexity.16

## **9. The Syntax-Semantics Interface and Curry-Howard**

The interface with categorial grammar is characterized by the structural preservation properties of mappings from syntactic types to semantic representations.6 This is viewed as an extension of the Curry-Howard correspondence, where syntactic derivations are interpreted as terms of the simply typed linear lambda calculus.6  
In this framework, the logical rules of the Lambek calculus act as a "glue" for semantic composition.34 Every step in a syntactic proof corresponds to a combinatory operation in the lambda calculus.25 This approach provides a systematic relation between syntax and semantics that is stricter than the usual notion of compositionality.5 For example, the transformation from a syntactic sequent to a semantic reading is a homomorphism relating the syntactic source calculus and a target calculus for meaning assembly.6  
Structural preservation is particularly important in symmetric versions of categorial grammar, such as the Lambek-Grishin calculus.33 This system augments the standard connectives with a dual family (coproduct, left and right difference) and interaction laws like distributivity.33 These laws have been shown to enjoy stability of interpretations for Curry-Howard semantics and structural preservation at the syntactic end, offering a way to reconcile the demands of natural language form and semantic meaning.33

### **Table 6: The Curry-Howard Correspondence in Categorial Type Logic**

| Syntactic Component | Semantic Counterpart | Logical Role |
| :---- | :---- | :---- |
| **Atomic Type** | Semantic Type | Basic Category |
| **Slash ( \\ or / )** | Function Type ( [formula omitted in source conversion] ) | Implication / Application |
| **Product ( [formula omitted in source conversion] )** | Product Type ( [formula omitted in source conversion] ) | Conjunction / Pairing |
| **Derivation** | Lambda Term | Proof as Program |
| **Cut-Elimination** | Beta-Reduction | Computational Normalization |

The correspondence also allows for the adaptation of linear logic "proof nets" to the Lambek calculus.25 Proof nets provide efficient parsing algorithms by identifying proofs that are equivalent up to "spurious" permutations of rules.25 Conceptually, this proof syntax serves as a justification for the "parsing as deduction" paradigm, ensuring that only proofs corresponding to different syntactic analyses are distinguished.25

## **10. Canonical Objectives and Future Directions**

The maturation of the structural theory of the Lambek calculus depends on resolving several "canonical targets" that would force a fundamental rewriting of the standard summary of the theory.2

1. **Algebraic Foundations of Completeness**: Moving beyond standard L-models to understand why certain extensions fail to be complete with respect to linguistically natural models.13 This involves identifying the specific algebraic properties—such as the failure of distributivity or the role of the multiplicative unit—that create gaps between derivability and validity.15  
2. **Mapping the Decidability Frontier**: Identifying the precise combination of structural rules and connectives that leads to undecidability.15 The jump from PTIME to NP-complete to hyper-Ackermannian complexity needs a unified explanation grounded in the essential structure of the logic rather than instance-specific claims.2  
3. **Formalizing Structural Preservation**: Formulating rigorous properties for the syntax-semantic mapping.6 This includes exploring how the "molecular connectives" of display calculi or the structural morphisms of skew monoidal categories can maintain semantic coherence in the presence of non-invertible structural laws.16  
4. **Integration of Hypergraph Grammars**: Elevating the interplay between substructural logics and formal grammars to first-order systems like MILL1.11 This involves characterizing the expressive power of these systems in terms of hypergraph replacement grammars and understanding the complexity of their derivability problems.11

By adhering to the constraints of temporal durability and closeness to established notation, the structural theory will remain a valuable framework for both logic and linguistics.2 The focus must remain on claims of high abstraction—such as the relationship between structural rules and language recognition—rather than on fashionable but fleeting computational techniques.7 Grounding results in the essential structure of the logic itself ensures that the Lambek calculus continues to serve as a beacon for the study of resource-sensitive reasoning in all its forms.

## **11. Conclusion: Synthesizing the Structural Theory**

The Lambek calculus stands as the archetype of a structure-sensitive logic, providing a precise mechanism for managing the order and multiplicity of informational resources. Its structural theory is not a collection of isolated facts but a unified landscape where the removal of structural rules reveals the underlying fabric of both formal languages and logical deduction. The transition from the non-associative groupoids of NL to the associative strings of L and the commutative multisets of LP maps directly onto the complexity and recognitional power of our most sophisticated grammatical theories.  
As we move forward, the focus on meta-theorems like cut-elimination, the discovery of invertibility through focusing, and the rigorous proof of completeness limits will provide the necessary rigor to sustain this research agenda. The interface with the Curry-Howard correspondence ensures that the logic of syntax is never divorced from the logic of meaning, while the exploration of first-order extensions like MILL1 pushes the boundaries of what these systems can represent. By systematically addressing the canonical targets identified here, the community will continue to build a theory that is not only mathematically elegant but also fundamentally insightful regarding the structural nature of information itself.

## **Works Cited**

1. Substructural logics \- University of St Andrews Research Portal, accessed on April 11, 2026, [https://research-portal.st-andrews.ac.uk/en/publications/substructural-logics/](https://research-portal.st-andrews.ac.uk/en/publications/substructural-logics/)  
2. Complexity of the Lambek Calculus and Its Extensions, accessed on April 11, 2026, [https://staff.math.su.se/rloukanova/LACompLing2021-web/slides-LACompLing2021/StepanKuznetsov-LACompLing2021.pdf](https://staff.math.su.se/rloukanova/LACompLing2021-web/slides-LACompLing2021/StepanKuznetsov-LACompLing2021.pdf)  
3. Substructural Logics (Stanford Encyclopedia of Philosophy/Spring 2025 Edition), accessed on April 11, 2026, [https://plato.stanford.edu/archives/spr2025/entries/logic-substructural/](https://plato.stanford.edu/archives/spr2025/entries/logic-substructural/)  
4. Logical Inferentialism & Attacks on Classical Logic \- arXiv, accessed on April 11, 2026, [https://arxiv.org/pdf/2506.04295](https://arxiv.org/pdf/2506.04295)  
5. The Lambek Calculus \- DSpace, accessed on April 11, 2026, [https://dspace.library.uu.nl/bitstream/handle/1874/629/c8.pdf](https://dspace.library.uu.nl/bitstream/handle/1874/629/c8.pdf)  
6. Typelogical Grammar \- Stanford Encyclopedia of Philosophy, accessed on April 11, 2026, [https://plato.stanford.edu/entries/typelogical-grammar/](https://plato.stanford.edu/entries/typelogical-grammar/)  
7. 1 Substructural logics and structural modalities, accessed on April 11, 2026, [https://www.cs.upc.edu/\~morrill/papers/heads\_phrases.pdf](https://www.cs.upc.edu/~morrill/papers/heads_phrases.pdf)  
8. Substructural Logic: Understanding the roles of Weakening and Contraction, accessed on April 11, 2026, [https://math.stackexchange.com/questions/3356302/substructural-logic-understanding-the-roles-of-weakening-and-contraction](https://math.stackexchange.com/questions/3356302/substructural-logic-understanding-the-roles-of-weakening-and-contraction)  
9. SUBEXPONENTIALS IN NONASSOCIATIVE LAMBEK CALCULUS Eben Blaisdell A DISSERTATION in Mathematics Presented to the Faculties of the \- University of Pennsylvania, accessed on April 11, 2026, [https://repository.upenn.edu/bitstreams/c318a63b-b658-45b1-a8d3-ff6378032ab1/download](https://repository.upenn.edu/bitstreams/c318a63b-b658-45b1-a8d3-ff6378032ab1/download)  
10. the lambek calculus enriched with, accessed on April 11, 2026, [https://eprints.illc.uva.nl/1167/1/LP-1991-04.text.pdf](https://eprints.illc.uva.nl/1167/1/LP-1991-04.text.pdf)  
11. First-Order Intuitionistic Linear Logic and Hypergraph Languages \- DROPS, accessed on April 11, 2026, [https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/LIPIcs.ICALP.2025.170/LIPIcs.ICALP.2025.170.pdf](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/LIPIcs.ICALP.2025.170/LIPIcs.ICALP.2025.170.pdf)  
12. Non-commutative linear logic fragments with sub-context-free complexity \- arXiv, accessed on April 11, 2026, [https://arxiv.org/pdf/2511.02348](https://arxiv.org/pdf/2511.02348)  
13. Lambek Calculus and Formal Languages \- Cambridge University Press & Assessment, accessed on April 11, 2026, [https://resolve.cambridge.org/core/services/aop-cambridge-core/content/view/E60E1B6CD19E44AC69A80DD2E2B1FCF7/9781316716830c14\_p269-272\_CBO.pdf/lambek\_calculus\_and\_formal\_languages.pdf](https://resolve.cambridge.org/core/services/aop-cambridge-core/content/view/E60E1B6CD19E44AC69A80DD2E2B1FCF7/9781316716830c14_p269-272_CBO.pdf/lambek_calculus_and_formal_languages.pdf)  
14. complexity of the infinitary lambek calculus with kleene star \- Semantic Scholar, accessed on April 11, 2026, [https://www.semanticscholar.org/paper/COMPLEXITY-OF-THE-INFINITARY-LAMBEK-CALCULUS-WITH-Kuznetsov/0145edddab97e91df00102e7d7b08db4338ae5ad](https://www.semanticscholar.org/paper/COMPLEXITY-OF-THE-INFINITARY-LAMBEK-CALCULUS-WITH-Kuznetsov/0145edddab97e91df00102e7d7b08db4338ae5ad)  
15. Complexity of Nonassociative Lambek Calculus with Classical and Intuitionistic Logic \- Journals University of Lodz, accessed on April 11, 2026, [https://czasopisma.uni.lodz.pl/bulletin/article/download/24543/28360](https://czasopisma.uni.lodz.pl/bulletin/article/download/24543/28360)  
16. An Introduction to Substructural Logics \- ResearchGate, accessed on April 11, 2026, [https://www.researchgate.net/publication/238740721\_An\_Introduction\_to\_Substructural\_Logics](https://www.researchgate.net/publication/238740721_An_Introduction_to_Substructural_Logics)  
17. Decidability and complexity for substructural logics with weakening or contraction, accessed on April 11, 2026, [https://archive.illc.uva.nl/alg-coalg/slides/ramanayake-2021.pdf](https://archive.illc.uva.nl/alg-coalg/slides/ramanayake-2021.pdf)  
18. \[2104.09716\] Decidability and Complexity in Weakening and Contraction Hypersequent Substructural Logics \- arXiv, accessed on April 11, 2026, [https://arxiv.org/abs/2104.09716](https://arxiv.org/abs/2104.09716)  
19. \[PDF\] On the Lambek Calculus with an Exchange Modality \- Semantic Scholar, accessed on April 11, 2026, [https://www.semanticscholar.org/paper/On-the-Lambek-Calculus-with-an-Exchange-Modality-Jiang-Eades/0cc8850dba060db2ab4b05d8b55e15cfc36cb976](https://www.semanticscholar.org/paper/On-the-Lambek-Calculus-with-an-Exchange-Modality-Jiang-Eades/0cc8850dba060db2ab4b05d8b55e15cfc36cb976)  
20. On Logics Without Contraction \- Greg Restall, accessed on April 11, 2026, [https://consequently.org/papers/onlogics.pdf](https://consequently.org/papers/onlogics.pdf)  
21. Word order variability in OV languages : a study on scrambling, verb movement, and postverbal elements with a focus on Uralic la, accessed on April 11, 2026, [https://d-nb.info/1336627085/34](https://d-nb.info/1336627085/34)  
22. On the Lambek Calculus with an Exchange Modality \- arXiv, accessed on April 11, 2026, [https://arxiv.org/abs/1904.06847](https://arxiv.org/abs/1904.06847)  
23. Semi-Substructural Logics with Additives \- cgi .cse. unsw. edu.a u, accessed on April 11, 2026, [https://cgi.cse.unsw.edu.au/\~eptcs/paper.cgi?LSFA2023.8.pdf](https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?LSFA2023.8.pdf)  
24. Semi-Substructural Logics with Additives \- arXiv.org, accessed on April 11, 2026, [https://arxiv.org/html/2404.14922v1](https://arxiv.org/html/2404.14922v1)  
25. The Logic of Categorial Grammars: A Deductive Account of Natural Language Syntax and Semantics | Request PDF \- ResearchGate, accessed on April 11, 2026, [https://www.researchgate.net/publication/230651826\_The\_Logic\_of\_Categorial\_Grammars\_A\_Deductive\_Account\_of\_Natural\_Language\_Syntax\_and\_Semantics](https://www.researchgate.net/publication/230651826_The_Logic_of_Categorial_Grammars_A_Deductive_Account_of_Natural_Language_Syntax_and_Semantics)  
26. Formal Foundations of Linguistic Theory \- Scott Martin, accessed on April 11, 2026, [https://www.coffeeblack.org/publications/Pollard-Martin-FFLT.pdf](https://www.coffeeblack.org/publications/Pollard-Martin-FFLT.pdf)  
27. L-models and R-models for Lambek Calculus Enriched with ..., accessed on April 11, 2026, [https://homepage.mi-ras.ru/\~sk/wissenschaft/L-R-mod\_WoLLIC19\_selfarchive.pdf](https://homepage.mi-ras.ru/~sk/wissenschaft/L-R-mod_WoLLIC19_selfarchive.pdf)  
28. AiML 2022 Abstracts of short presentations, accessed on April 11, 2026, [https://aiml2022.irisa.fr/files/2023/01/AiML2022\_abstractsOfShortPresentations.pdf](https://aiml2022.irisa.fr/files/2023/01/AiML2022_abstractsOfShortPresentations.pdf)  
29. (PDF) Lambek Calculus is L-complete \- ResearchGate, accessed on April 11, 2026, [https://www.researchgate.net/publication/243779452\_Lambek\_Calculus\_is\_L-complete](https://www.researchgate.net/publication/243779452_Lambek_Calculus_is_L-complete)  
30. Strong completeness of the Lambek Calculus with respect to Relational Semantics \- SciSpace, accessed on April 11, 2026, [https://scispace.com/pdf/strong-completeness-of-the-lambek-calculus-with-respect-to-tm00ro1ts3.pdf](https://scispace.com/pdf/strong-completeness-of-the-lambek-calculus-with-respect-to-tm00ro1ts3.pdf)  
31. Sequents and Trees (Andrzej Indrzejczak) \- Tianren Liu, accessed on April 11, 2026, [https://www.liutianren.com/discrete/ref/Logic%20and%20Set%20Theory/Sequents%20and%20Trees%20(Andrzej%20Indrzejczak).pdf](https://www.liutianren.com/discrete/ref/Logic%20and%20Set%20Theory/Sequents%20and%20Trees%20\(Andrzej%20Indrzejczak\).pdf)  
32. Separation Logic with One Quantified Variable | Request PDF, accessed on April 11, 2026, [https://www.researchgate.net/publication/267468925\_Separation\_Logic\_with\_One\_Quantified\_Variable](https://www.researchgate.net/publication/267468925_Separation_Logic_with_One_Quantified_Variable)  
33. Semantic Representations for Multilingual Natural Language Processing | Request PDF \- ResearchGate, accessed on April 11, 2026, [https://www.researchgate.net/publication/340812278\_Semantic\_Representations\_for\_Multilingual\_Natural\_Language\_Processing](https://www.researchgate.net/publication/340812278_Semantic_Representations_for_Multilingual_Natural_Language_Processing)  
34. Course descriptions \- esslli 2025, accessed on April 11, 2026, [https://2025.esslli.eu/courses-workshops-accepted/course-information.html](https://2025.esslli.eu/courses-workshops-accepted/course-information.html)
