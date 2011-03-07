(** Basic definitions and theorems about weak equivalences. *)

Require Import HomotopyDefinitions.

(** For compatibility with Coq 8.2 we unset automatic parameter introduction. *)

Unset Automatic Introduction.

(** The identity map is a weak equivalence. *)

Definition idweq A : wequiv A A.
Proof.
  intro A.
  exists (idmap A).
  intros x.
  contract_hfiber x (idpath x).
  apply total_paths with (p := q).
  simpl.
  compute in q.
  path_induction.
Defined.

(** Every path between spaces gives a weak equivalence. *)

Definition path_to_weq {U V} : U ~~> V -> wequiv U V.
Proof.
  intros U v.
  intro p.
  induction p as [S].
  exact (idweq S).
Defined.

(** From a weak equivalence from [U] to [V] we can extract a map in the inverse direction. *)

Definition weq_inv {U V} : wequiv U V -> (V -> U).
Proof.
  intros U V.
  intros [w H] y.
  destruct (H y) as [[x p] _].
  exact x.
Defined.

(** The extracted map in the inverse direction is actually an inverse (up to homotopy, of
   course). *)

Lemma weq_inv_is_section U V (w : wequiv U V) : forall y : V, w (weq_inv w y) ~~> y.
Proof.
  intros U V w.
  intro y.
  destruct w as [w G].
  simpl.
  destruct (G y) as [[x p] c].
  exact p.
Defined.

Lemma weq_inv_is_retraction U V (w : wequiv U V) : forall x : U, (weq_inv w (w x)) ~~> x.
Proof.
  intros U V w.
  intro x.
  destruct w as [w H].
  simpl.
  destruct (H (w x)) as [[y p] c].
  assert (q := c (existT _ x (idpath (w x)))).
  assert (r := base_path q).
  exact (!r).
Defined.

(** The last general fact about weak equivalences that we need is that they are injective
   on paths, which is not too surprising, given that they have sections. *)

Lemma weq_injective U V : forall (w : wequiv U V) x y, w x ~~> w y -> x ~~> y.
Proof.
  intros U V.
  intros w x y.
  simpl.
  intro p.
  assert (q := map (weq_inv w) p).
  path_via (weq_inv w (w x)).
  apply opposite; apply weq_inv_is_retraction.
  path_via (weq_inv w (w y)).
  apply weq_inv_is_retraction.
Defined.

