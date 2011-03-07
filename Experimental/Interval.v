(** Peter Lumsdaine's interval. *)

Add LoadPath "../UnivalentFoundations".

Require Import Homotopy.

Unset Automatic Introduction.

(** The interval is a Type. *)

(** printing Interval $[0,1]$ #[0,1]# *)

Axiom Interval : Type.

(** The interval has two endpoints and a path between them. *)

(** printing zero $0$ #0# *)
(** printing one  $1$ #1# *)
(** printing segment  $\vec{01}$ #1# *)

Axiom zero : Interval.
Axiom one : Interval.
Axiom segment : zero ~~> one.

(** As a warmup we first write down the non-dependent version of the interval. *)

(** A path [p : a ~~> b] in [X] induces a function [Interval -> X] with desired properties. *)

Axiom interval_path' : forall {X} {a b : X} (p : a ~~> b), Interval -> X.

Axiom interval_path_zero' : forall {X} {a b : X} (p : a ~~> b), interval_path' p zero ~~> a.
Axiom interval_path_one' : forall {X} {a b : X} (p : a ~~> b), interval_path' p one ~~> b.

Axiom interval_path_segment' : forall X (a b : X) (p : a ~~> b),
  !(interval_path_zero' p) @ map (interval_path' p) segment @ (interval_path_one' p) ~~> p.

(** However these simple rules will not be enough. We need a suitable fibered version in which
   the target space is parametrized by the interval. *)

Axiom interval_path : forall {P : Interval -> Type} {a : P zero} {b : P one} (p : transport segment a ~~> b),
  forall x, P x.

Axiom interval_path_zero : forall {P : Interval -> Type} {a : P zero} {b : P one} (p : transport segment a ~~> b),
  interval_path p zero ~~> a.

Axiom interval_path_one : forall {P : Interval -> Type} {a : P zero} {b : P one} (p : transport segment a ~~> b),
  interval_path p one ~~> b.

Axiom interval_path_segment : forall {P : Interval -> Type} {a : P zero} {b : P one} (p : transport segment a ~~> b),
  !(interval_path_zero' p) @ map (interval_path' p) segment @ (interval_path_one' p) ~~> p.

(** This lemma is missing from basic facts and needs to be added. *)
Lemma self_transport_path A (x y : A) (p : x ~~> y) : transport (P := fun z => z ~~> y) p p ~~> idpath y.
Proof.
  path_induction.
Defined.

Theorem Interval_contractible : contractible Interval.
Proof.
  split with one.
  intro t.
  apply @interval_path with
    (P := fun x => x ~~> one) (a := segment) (b := idpath one).
  apply self_transport_path.
Defined.

(** And another lemma which should be in the main library. *)
Lemma transport_in_trivial_fibration {A B} {x y : A} (p : x ~~> y) (u : B) :
  transport (P := fun _ => B) p u ~~> u.
Proof.
  path_induction.
Defined.

Definition twist : Interval -> Interval.
Proof.
Print interval_path.
  apply @interval_path with (a := one) (b := zero).
  path_via one.
  apply transport_in_trivial_fibration.
  exact (!segment).
Defined.

Lemma twist_involution : forall t : Interval, twist (twist t) ~~> t.
Proof.
  intro t.
  destruct Interval_contractible as [c p].
  path_via c.
Defined.
