(declare-sort Pose 0)
(declare-fun Pose_x (Pose) Real)
(declare-fun Pose_y (Pose) Real)
(declare-fun Pose_theta (Pose) Real)

(declare-sort Trj 0)
(declare-fun poseAt (Trj Real) Pose)
(declare-fun Trj_length (Trj) Real)

(declare-fun InBall (Pose Pose Real) Bool)
(assert
    (forall ((p1 Pose) (p2 Pose) (delta1 Real) (delta2 Real)) 
        (=> 
            (and (>= delta1 0) (>= delta2 0) (<= delta1 delta2))
            (=> (InBall p1 p2 delta1) (InBall p1 p2 delta2))
        )
    )
)
(assert
    (forall ((p1 Pose) (p2 Pose) (delta Real)) 
        (=> 
            (>= delta 0) 
            (= (InBall p1 p2 delta) (InBall p2 p1 delta))
        )
    )
)

(assert
    (forall ((p1 Pose) (p2 Pose) (p3 Pose) (delta1 Real) (delta2 Real)) 
        (=> 
            (>= delta1 0) (>= delta2 0)
            (=> (and (InBall p1 p2 delta1) (InBall p2 p3 delta2)) (InBall p1 p3 (+ delta1 delta2)))
        )
    )
)

(declare-sort ActTrj 0)
(declare-sort Act 0)
(declare-fun actAt (ActTrj Real) Act)
(declare-fun ActTrj_length (ActTrj) Real)

(declare-sort SimpleCar 0)
(declare-fun L (SimpleCar) Real)
(declare-fun dyn (SimpleCar Pose ActTrj) Trj)

(declare-fun intg (Real) Real)

(declare-sort TF 0)
(declare-fun TF_trj (TF) Trj)
(declare-fun TF_a (TF) ActTrj)
(declare-fun TF_shat (TF) Trj)
(declare-fun TF_env (TF) SimpleCar)
(declare-fun TF_ctrl (Trj Trj) ActTrj)

(declare-const delta  Real)
(assert (>= delta 0))
(declare-const lb  Real)
(declare-const ub  Real)

(define-fun A_TF ((tf TF)) Bool
    (and 
        (forall ((init Pose) (t Real)) 
            ; (InBall (poseAt (TF_shat tf) t) (poseAt (dyn (TF_env tf) (poseAt (TF_shat tf) 0) (TF_a tf)) t) delta )
            (InBall (poseAt (TF_shat tf) t) (poseAt (dyn (TF_env tf) init (TF_a tf)) t) (* 2 delta) ) 
        )
        (>= (L (TF_env tf)) lb) (<= (L (TF_env tf)) ub)
        (= (poseAt (TF_shat tf) 0) (poseAt (TF_trj tf) 0))
    )
)

(define-fun G_TF ((tf TF)) Bool
    (forall ((p Real))
                (=> (and (>= p 0) (<= p (Trj_length (TF_trj tf)))) 
                    (exists ((t Real))
                        (and
                            (= p (intg t))
                            (InBall (poseAt (dyn (TF_env tf) (poseAt (TF_shat tf) 0) (TF_a tf)) t) (poseAt (TF_trj tf) p) delta)
                        ) 
                    )
                )
            )
)

(define-fun Gnf_TF ((tf TF)) Bool 
    (=> (A_TF tf) (G_TF tf))
)


(declare-sort ENV 0)
(declare-fun ENV_a (ENV) ActTrj)
(declare-fun ENV_xi (ENV) Trj)
(declare-fun ENV_env (ENV) SimpleCar)
(define-fun A_ENV ((env ENV)) Bool
    true
)
(define-fun G_ENV ((env ENV)) Bool
    (and (forall ((init Pose)(t Real)) 
            ;;(InBall (poseAt (ENV_xi env) t) (poseAt (dyn (ENV_env env) (poseAt (ENV_xi env) 0) (ENV_a env)) t)  delta ) 
            (InBall (poseAt (ENV_xi env) t) (poseAt (dyn (ENV_env env) init (ENV_a env)) t)  delta ) 
        )
        (>= (L (ENV_env env)) lb) (<= (L (ENV_env env)) ub))
)

(define-fun Gnf_ENV ((env ENV)) Bool 
    (=> (A_ENV env) (G_ENV env))
)

(declare-sort SE 0)
(declare-fun SE_xi (SE) Trj)
(declare-fun SE_shat (SE) Trj)

(define-fun A_SE ((se SE)) Bool
    true
)
(define-fun G_SE ((se SE)) Bool
  (forall ((t Real)) 
    (InBall (poseAt (SE_shat se) t) (poseAt (SE_xi se) t)  delta ) 
  )
)

(define-fun Gnf_SE ((se SE)) Bool 
    (=> (A_SE se) (G_SE se))
)

(declare-sort TES 0)
(declare-fun TES_trj (TES) Trj)
(declare-fun TES_xi (TES) Trj)
(declare-fun TES_shat (TES) Trj)


(define-fun A_TES ((tes TES)) Bool
    (= (poseAt (TES_shat tes) 0) (poseAt (TES_trj tes) 0))
)
(define-fun G_TES ((tes TES)) Bool
  (forall ((p Real))
                (=> (and (>= p 0) (<= p (Trj_length (TES_trj tes)) )) 
                    (exists ((t Real))
                        (and
                            (= p (intg t))
                            (InBall (poseAt (TES_xi tes) t) (poseAt (TES_trj tes) p) (* 2 delta))
                        ) 
                    )
                )
            )
)

(declare-fun TES_tf (TES) TF)
(declare-fun TES_env (TES) ENV)
(declare-fun TES_se (TES) SE)

(declare-const tes TES)

; Connections
(assert 
    (and
        (= (TES_trj tes) (TF_trj (TES_tf tes)))
        (= (TES_xi tes) (ENV_xi (TES_env tes)))
        (= (TF_a (TES_tf tes)) (ENV_a (TES_env tes)))
        (= (TF_env (TES_tf tes)) (ENV_env (TES_env tes)))
        (= (ENV_xi (TES_env tes)) (SE_xi (TES_se tes)))
        (= (SE_shat (TES_se tes)) (TF_shat (TES_tf tes)))
        (= (TES_shat tes) (SE_shat (TES_se tes)))
    )
)

(push)
(assert 
    (not
        (=>
            (and
                (A_TES tes)
                (Gnf_ENV (TES_env tes))
                (Gnf_SE (TES_se tes))
            )
            (A_TF (TES_tf tes))
        )
    )
)

(check-sat)
(pop)
(push)
(assert 
    (not
        (=>
            (and
                (A_TES tes)
                (Gnf_TF (TES_tf tes))
                (Gnf_ENV (TES_env tes))
                (Gnf_SE (TES_se tes))
            )
            (G_TES tes)
        )
    )
)
(check-sat)
