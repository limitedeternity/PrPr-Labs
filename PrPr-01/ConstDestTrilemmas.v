Theorem ex54_16: forall a1 a2 a3 b c : Prop,
                 (a1 -> b) -> (a2 -> b) -> (a3 -> b) -> 
                 (a1 \/ a2 \/ a3) -> b.
Proof.
  intros. elim H2. intro. apply (H H3).
  intro. elim H3. intro. apply (H0 H4).
  intro. apply (H1 H4).
Qed.

Theorem ex54_17: forall a1 a2 a3 b1 b2 b3: Prop,
                 (a1 -> b1) -> (a2 -> b2) -> (a3 -> b3) ->
                 (a1 \/ a2 \/ a3) -> (b1 \/ b2 \/ b3).
Proof.
  intros. elim H2. intro. left. apply (H H3).
  intro. elim H3. intro. right. left. apply (H0 H4).
  intro. right. right. apply (H1 H4).
Qed.

Theorem ex54_18: forall a b1 b2 b3 : Prop,
                 (a -> b1) -> (a -> b2) -> (a -> b3) -> 
                 (~b1 \/ ~b2 \/ ~b3) -> ~a.
Proof.
  intros. intro. elim H2. intro. apply H4.
  apply (H H3). intro. elim H4. intro.
  apply H5. apply (H0 H3). intro.
  apply H5. apply (H1 H3).
Qed.

Theorem ex54_19: forall a1 a2 a3 b1 b2 b3 : Prop,
                 (a1 -> b1) -> (a2 -> b2) -> (a3 -> b3) -> 
                 (~b1 \/ ~b2 \/ ~b3) -> (~a1 \/ ~a2 \/ ~a3).
Proof.
  intros. elim H2. intro. left. intro.
  apply H3. apply (H H4).
  intro. elim H3. intro. right. left. intro.
  apply H4. apply (H0 H5).
  intro. right. right. intro. apply H4.
  apply (H1 H5).
Qed.
