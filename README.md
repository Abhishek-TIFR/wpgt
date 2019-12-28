# List-Set 
This work aims to formally verify the weak perfect graph theorems (WPGT) in the Coq proof assistant. 

There is an accompanying paper describing this formalization titled:
- Title: A Constructive Formalization of the Weak Perfect Graph Theorem.  (CPP'20).
- Abstract: The Perfect Graph Theorems are among the most important results in graph theory 
  describing the relationship between clique number $\omega(G)$ and chromatic number $\chi(G)$ of a 
  graph G. A graph G is called perfect if $\omega(H) = \chi(H)$ for every induced subgraph H of G. The 
  Strong Perfect Graph Theorem (SPGT) states that a graph is perfect if and only if it does not
  contain an odd hole (or an odd anti-hole) as its induced subgraph. The Weak Perfect Graph 
  Theorem (WPGT) states that a graph is perfect if and only if its complement is perfect. In this
  work, we consider the Weak Perfect Graph Theorem and present a formal framework for its 
  verification. We model  finite simple graphs in the Coq Proof Assistant by representing its 
  vertices as  finite sets over a countably infinite domain. We argue that this approach provides 
  a formal framework in which it is convenient to work with different types of graph constructions 
  (or expansions) involved in the proof of the Lovász Replication Lemma (LRL), which is also 
  the key result used in the proof of Weak Perfect Graph Theorem. Finally, we use this setting to 
  develop a constructive formalisation of the Weak Perfect Graph Theorem.
  
The project is split into the following Coq files: 

1. GenReflect.v: Contains common results on reflection techniques.

2. SetSpecs.v: Common predicates over sets.

3. Sorting.v: Sorting a list using a decidable binary relation.

4. MinMax.v: Min and Max in a list.

5. DecType.v: Type with decidable equality. 

6. SetReflect.v: Reflection lemmas for sets on decidable types

7. DecList.v: Lists on decidable types

8.  OrdType.v: A type with decidable equality and ordering among elements.

9. OrdList.v: Lists of elements of ordType

10. OrdSet.v: Sets as ordered lists 

11. SetMaps.v: Functions over sets

12. Powerset.v: Power sets as sets

13. SetCover.v: Covering a set using a collection of sets

14. UG.v: Undirected graphs with decidable edge relations.

15. MoreUG.v: Graph theory on decidable undirected graphs

16. GenIso.v: Graph Isomorphism  

17. GraphCovers.v: Covering a graph using cliques and stable sets

18. Repeat.v: Definition of vertex repetition as a relation

19. LovaszRep.v:  Lovasz Replication Lemma Proof for one vertex expansion

20. LovaszExp.v:  Lovasz Replication Lemma Proof for general expansion

21. WeakPerfect.v: Proof of the Weak Perfect Graph Theorem



- The file sets.sh can be used to compile the files on sets and power sets (i.e. up to Powerset.v). 

- The file graphs.sh can be used to compile the files on undirected graphs (i.e. UG.v, MoreUG.v, GenIso.v, and GraphCovers.v). 

- To compile the whole project run all.sh. 
