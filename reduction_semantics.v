Require Import Relations.
Require Import Program.
Require Import rewriting_system.


(* Note: The only grammar mentioned in this formalization is a grammar of evaluation
   contexts, thus any reference to a grammar means the grammar of contexts of 
   the formalized language.
   
   In this formalisation we represent evaluation contexts in terms of elementary
   contexts (if you do not understand this go to the paper). To obtain the grammar 
   proper for this formalization first translate the original grammar to a form, 
   where each right side of a production is a hole or it has a context non-terminal.
   Now if you take each non-hole right side and replace the context symbol by a hole,
   you will a set of get context patterns that identify needed elementary contexts - 
   we will use EC markings for these patterns.

   E.g., if k1, k2 are context non-terminals and there is a production  k1 -> a b k2 c,
   then the coresponding context pattern is  a b [] c  .

   Unfortunatly, not all such grammars are proper for our formalisation, so we may 
   still need to refine them. If we try to say it intuitivly, the grammars describe 
   automata on words build from elementary contexts and these automata need to be 
   deterministic.

   Saying it less intuitvaly: for any context non-teminal symbol k and elem. context ec 
   there needs to be at most one k' such that there exists a production  k -> EC[k']  
   and ec matches EC. Let us call such grammars >deterministic grammars of contexts<. 

   You may achive this form by spliting the context patterns and determinizing 
   the grammar.

   E.g., suppose you have a grammar with two productions form k1:  k1 -> a k2 a,  
   k1 -> ab k3 ab,  where L(a), L(b) are disjoint languages and L(ab) = L(a) U L(b). 
   Then you may split the second pattern  ab [] ab  to:  a [] a,  b [] ab,  ab [] b. 
   So, the second production may be replaced by three other:  k1 -> a k3 a,  
   k -> b k3 ab,  k -> ab k3 b. And then you may determinize the grammar by the
   exponential construction. In this case, it will introduce a new context symbol 
   {k2,k3}, replacing the productions  k1 -> a k2 a,  k1 -> a k3 a  with  
   k1 -> a {k2,k3} a  and derivating the missing part of the grammar from the symbol
   {k2,k3}.

   In this formalisation contexts are treated as words of elementary contexts, where
   the end of a word means a hole. Because such a word may end in any place, this 
   enforces an additional condition on the grammars that, the production  k -> []  
   exists for any non-terminal k. However, this condition is not restrictive (keep
   reading).

   Definition: If a derivation of a context ends with a production  k -> [], then
   we say that the context has a >hole of the kind k<. 

   In this formalisation we may give a different set of redexes that may occure in 
   a hole per each hole kind. Hence, if there was no production  k -> [], then
   we may equivalently fix an empty set of redexes for this k. *)




(* Signature for languages with reduction semantics and multiple kinds of contextes. *)

Module Type RED_SEM.

  (* Preconditions: To instaniate this module you need to determinizethe grammar of 
     contextes. *)


  Parameter term : Set.
  Parameter elem_context : Set.
  Parameter ckind : Set. (* kinds of contexts, that is, non-terminal context symbols 
                            in the grammar *)


  (* ckind_trans - function that determinates the productions in the grammar, that is,
                   if ckind_trans k1 ec = k2, then k1 -> EC[k2] where ec matches EC or
                   there is no such production and k2 is a sink. 
                   In other words, it is the transition function of a finite automaton 
                   representing the totalized grammar. *)
  Parameter  ckind_trans : ckind -> elem_context -> ckind.
  Infix "+>" := ckind_trans (at level 50, left associativity).


  (* context k1 k2 - contexts of kind k1 (derivated from k1) with a hole of kind k2. 
                     Contexts are represented by reversed derivations in the grammar.
                     E.g., if a context is derivated by a sequence of productions
                     k1 -> ec1 k2, k2 -> ec2 k3, k3 -> ec3 k4, k4 -> [], then it is 
                     represented by the list  (ec3, k3), (ec2, k2), (ec1, k1)  of 
                     the type  context k1 k4.
                     The second elements in the pairs are implicite. *)
  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).


  (* Note: Contexts are reversed, because during evaluation by refocusing we always 
     access the elem. context nearest to the hole of a context. *)


  (* Definition: The hole of a context is >dead< if its kind is a sink symbol. *)

  (* Definition: A context is >proper< if its hole is not dead. 
     (Context with dead holes are contexts that cannot be generated in the orginal
     grammar.) *)



  (* Standard contexts composition: *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).



  (* Plugging is standard. You need to provide only plugging function for elem.
     contexts. *)

  Parameter elem_plug : term -> elem_context -> term.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).

  (* The following axiom, somehow, relates our representation of contexts to the 
     real eval. contexts, but generally we can instantiate the module with 
     elem. contexts that do not represent real elem. contexts and so not
     every module of this signature is a proper. *)
  Axiom elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.


  (* An intuitive definition: *)
  Definition immediate_ec ec t := exists t', ec:[t'] = t.


  (* redex k - representations of redexes that may occur in a hole of the kind k. 
     value k where k is not a sink
             - (almost) normal forms of kind k, that is, representations of terms
               that cannot be decomposed to a context k k' and a redex k'.  value k
               where k is a sink may be anything. *)
  Parameters value redex : ckind -> Set.

  Parameter value_to_term : forall {k}, value k -> term.
  Coercion  value_to_term : value >-> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Coercion  redex_to_term : redex >-> term.

  Axiom value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.




  Parameter  init_ckind : ckind.         (* start symbol in the grammar *)
  Parameter  dead_ckind : ckind -> Prop. (* set of sink symbols; if your grammar
                                            is not total you need to introduce at least
                                            one *)

  (* The sink property: *)
  Axiom death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).
  (* A key property of sink non-terminals: *)
  Axiom proper_death : 
      forall k, dead_ckind k -> ~ exists (r : redex k), True.




  (* Definition: A decomposition c[t] is empty if c is empty. *)
  (* Definition: A decomposition c[t] is proper if c is proper. *)


  (* Axioms of normal forms: *)
  Axiom value_trivial1 : forall {k} (v : value k) ec {t}, 
                             ~dead_ckind (k+>ec) -> ec:[t] = v -> 
                                 exists (v' : value (k+>ec)), t = v'.
  Axiom value_redex    : forall {k} (v : value k) (r : redex k), 
                             value_to_term v <> redex_to_term r.
  (*Axiom trivial_val_red : 
      forall k t, ~dead_ckind k -> only_trivial t k ->
         (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).*)


  (* decomp k  - decomposition of a term t from the symbol k to a redex.
     d_red r c  means: t = c[r].
     d_val v    means: t has no redexes and so it is a value, t = v. *)
  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.


  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red _ r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.


  Axiom decompose : forall (t : term) k, ~dead_ckind k -> 
                        exists d : decomp k, dec t k d.


  (* Reduction of a redex (it may get stuck): *)
  Parameter contract : forall {k}, redex k -> option term.


  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].


  Instance lrws : LABELED_REWRITING_SYSTEM :=
  { label := ckind; lconfiguration := term; ltransition := reduce }.

End RED_SEM.




Module Type RED_SEM_DET (R : RED_SEM).  Import R.
  Axiom dec_is_det : forall {t k} {d d0 : decomp k}, 
                         dec t k d -> dec t k d0 -> d = d0.
End RED_SEM_DET.
