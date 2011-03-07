(** Trying to naively define the interval in Coq is futile because the
   closed interval is weakly equivalent to the singleton. This file is
   an adaptation of Peter Lumsdaine's definition of interval. *)

(** This file is very much unfinished, and obviously parts of it will have
   to be moved to a library about contractible spaces. *)a

Add LoadPath "../UnivalentFoundations".

Require Import Homotopy.

(** Compatibility with Coq 8.2. *)

Unset Automatic Introduction.

(** Suppose we had a type Interval which looked like the usual
   closed interval, i.e., it had two points, a path between them
   and it satisfied the rules which say that paths in other spaces
   aries as images of the [Interval]. *)

(** printing ~~> $\leadsto$ *)
(** printing Interval $[0,1]$ #[0,1]# *)

Axiom Interval : Type.

(** The interval has two endpoints and a path between them. *)

(** printing zero $0$ #0# *)
(** printing one  $1$ #1# *)
(** printing segment  $\vec{01}$ #1# *)

Axiom zero : Interval.
Axiom one : Interval.
Axiom segment : zero ~~> one.

(** Every path arises as the action of a function from the interval. We need to write down a suitable
   dependent version which will allow us to show that the interval is contractible. *)

Axiom interval_path : forall {P : Interval -> Type} {a : P zero} {b : P one} (p : transport segment a ~~> b),
  forall x, P x.

(** Peter Lumsdaine's version also contains axioms which say how
   [interval_path] interacts with [zero], [one], and segment. But they
   are not needed as we show below. *)

(** The following three facts are missing from basic facts and needs to be added. *)

Definition dependent_map A {P : A -> Type} (f : forall x : A, P x) {x y : A} (p : x ~~> y) :
  transport p (f x) ~~> f y.
Proof.
  path_induction.
Defined.

Lemma self_transport_path A (x y : A) (p : x ~~> y) : transport (P := fun z => z ~~> y) p p ~~> idpath y.
Proof.
  path_induction.
Defined.

Lemma transport_in_trivial_fibration {A B} {x y : A} (p : x ~~> y) (u : B) :
  transport (P := fun _ => B) p u ~~> u.
Proof.
  path_induction.
Defined.

(** We can now prove that [Interval] is contractible, i.e.,
homotopically equivalent to a point. *)

Theorem Interval_contractible : contractible Interval.
Proof.
  split with one.
  intro t.
  apply @interval_path with
    (P := fun x => x ~~> one) (a := segment) (b := idpath one).
  apply self_transport_path.
Defined.

Lemma path_product {A} {B} {x y : A} {u v : B} :
  x ~~> y -> u ~~> v -> (x,u) ~~> (y,v).
Proof.
  path_induction.
Defined.

Theorem contractible_path_space A : contractible A -> contractible (path_space A).
Proof.
  intros A [c p].
  split with (existT _ (c,c) (idpath c)).
  intros [[x y] q].
  simpl in q.
  induction q.
  apply total_paths with (p := path_product (p x) (p x)).
  simpl.
  admit.
Defined.

Theorem contractible_induction A (P : path_space A -> Type) (c : contractible A) :
  P (existT _ (projT1 c) (projT1 c) (idpath (projT1 c))) -> forall x, P x.
Proof.
  intros A P [c p].
  intros u x.
  simpl in u.
  eapply @transport with (P := P) (x := c) (y := x).
  apply opposite; apply p. 
  assumption.
Defined.

Lemma path_between {A} : contractible A -> forall x y : A, x ~~> y.
Proof.
  intros A [c p] x y.
  path_via c.
Defined.

Lemma contractible_transport A (c : contractible A) (P : A -> Type) :
  forall (x y : A) (a : P x) (b : P y), transport (path_between c x y) a ~~> b.
Proof.
  intros A c P.
  apply (contractible_induction A
    (fun x => forall (y : A) (a : P x) (b : P y), transport (path_between c x y) a ~~> b) c).
  apply (contractible_induction A
    (fun y => forall (a : P (projT1 c)) (b : P y), transport (path_between c (projT1 c) y) a ~~> b) c).
  intros a b.
  path_via 




  intros A [c p] x y P a b.
  simpl.


(** The expected axioms for [Interval] now become easily provable, for
   example: *)

Lemma interval_path_zero : forall (P : Interval -> Type) (a : P zero) (b : P one) (p : transport segment a ~~> b),
  interval_path p zero ~~> a.
Proof.
  intros P a b p.

  eapply (@contractible_induction Interval
    (fun a => forall (b : P one) (p : transport segment a ~~> b), interval_path p zero ~~> a)
    Interval_contractible).



Axiom interval_path_one : forall {P : Interval -> Type} {a : P zero} {b : P one} (p : transport segment a ~~> b),
  interval_path p one ~~> b.

(** We omit the axiom which expresses the computation rule for [segment], as it is not needed. *)


