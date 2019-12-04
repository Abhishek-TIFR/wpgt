# List-Set 
This work aims to formally verify the weak perfect graph theorems (WPGT) in the Coq proof assistant. 

There is an accompanying paper describing this formalization titled:
 "A Constructive Formalization of the Weak Perfect Graph Theorem"
  - by Abhishek Kr Singh and Raja Natarajan (In the proceedings of CPP'20).
  
The project is split into the following files: 

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



The file sets.sh can be used to compile the files on sets and power sets (i.e. up to Powerset.v). 
The file graphs.sh can be used to compile the files on undirected graphs (i.e. UG.v, MoreUG.v, GenIso.v, and GraphCovers.v). 
To compile the whole project run all.sh. 
