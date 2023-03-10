; Pose datatype
(declare-sort Pose 0)
(declare-fun Pose_x (Pose) Real)
(declare-fun Pose_y (Pose) Real)
(declare-fun Pose_theta (Pose) Real)

; Trajectory type
(declare-sort Trj 0)
; Pose along the trajectory from the initial node to a given distance
(declare-fun poseAt (Trj Real) Pose)
; Total length of a trajectory
(declare-fun Trj_length (Trj) Real)

; Definition of a a neighborhood
(declare-fun InBall (Pose Pose Real) Bool)
; Containement
(assert
    (forall ((p1 Pose) (p2 Pose) (delta1 Real) (delta2 Real)) 
        (=> 
            (and (>= delta1 0) (>= delta2 0) (<= delta1 delta2))
            (=> (InBall p1 p2 delta1) (InBall p1 p2 delta2))
        )
    )
)
; Commutativity
(assert
    (forall ((p1 Pose) (p2 Pose) (delta Real)) 
        (=> 
            (>= delta 0) 
            (= (InBall p1 p2 delta) (InBall p2 p1 delta))
        )
    )
)
; Propagation of uncertainty
(assert
    (forall ((p1 Pose) (p2 Pose) (p3 Pose) (delta1 Real) (delta2 Real)) 
        (=> 
            (>= delta1 0) (>= delta2 0)
            (=> (and (InBall p1 p2 delta1) (InBall p2 p3 delta2)) (InBall p1 p3 (+ delta1 delta2)))
        )
    )
)
; Trajectories of actuator commands
(declare-sort ActTrj 0)
; Actuator command
(declare-sort Act 0)
; Actuator command at a given distance in the trajectory
(declare-fun actAt (ActTrj Real) Act)
; Totalk length of the trajectory of actuator commands
(declare-fun ActTrj_length (ActTrj) Real)

; The class of all simple car models 
(declare-sort SimpleCar 0)
; The legnth of a simple car
(declare-fun L (SimpleCar) Real)
; A function that given a simple car model, an initial pose, 
; and a trajectory of actuator commands computes a trajectory of poses
(declare-fun dyn (SimpleCar Pose ActTrj) Trj)
; Link between time and distance (in reality, this is an integral of the velocity function)
; we only need this to move from time to distance but its definition is not really needed 
; in the proofs.
(declare-fun intg (Real) Real)

;;;;;; COMPONENTS

; Trajectory follower
(declare-sort TF 0)
; Input trj
(declare-fun TF_trj (TF) Trj)
; Output a
(declare-fun TF_a (TF) ActTrj)
; Input \hat{s}
(declare-fun TF_shat (TF) Trj)
; Input environment model env
(declare-fun TF_env (TF) SimpleCar)
; Any positive delta would do
(declare-const delta  Real)
(assert (>= delta 0))

; lower and upper bound on the length of the car
(declare-const lb  Real)
(assert (>= lb 0))
(declare-const ub  Real)
(assert (>= ub 0))

; Assumptions of the trajectory follower
; - For all initial conditions, the environment behaves like a simple car
; - There are bounds on the uncertainty about the length of the car
; - The trajectory command starts at the state estimate
(define-fun A_TF ((tf TF)) Bool
    (and 
        (forall ((init Pose) (t Real)) 
            (InBall (poseAt (TF_shat tf) t) (poseAt (dyn (TF_env tf) init (TF_a tf)) t) (* 2 delta) ) 
        )
        (>= (L (TF_env tf)) lb) (<= (L (TF_env tf)) ub)
        (= (poseAt (TF_shat tf) 0) (poseAt (TF_trj tf) 0))
    )
)
; Guarantees of the trajectory follower:
; - The generated actuator commands are such that the state estimate follows the trajectory
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
; Saturated guarantee
(define-fun Gnf_TF ((tf TF)) Bool 
    (=> (A_TF tf) (G_TF tf))
)

; Environment component
(declare-sort ENV 0)
; Input a
(declare-fun ENV_a (ENV) ActTrj)
; Output trajectory \xi
(declare-fun ENV_xi (ENV) Trj)
; Environment model env
(declare-fun ENV_env (ENV) SimpleCar)
; Assumptions of the environment
; - The environment makes no assumptions
(define-fun A_ENV ((env ENV)) Bool
    true
)
; Guarantees of the environment
; - The car length has bounded uncertainty
; - The state follows the behavior of a simple car for all initial conditions
(define-fun G_ENV ((env ENV)) Bool
    (and (forall ((init Pose)(t Real)) 
            (InBall (poseAt (ENV_xi env) t) (poseAt (dyn (ENV_env env) init (ENV_a env)) t)  delta ) 
        )
        (>= (L (ENV_env env)) lb) (<= (L (ENV_env env)) ub))
)
; Saturated guarantee
(define-fun Gnf_ENV ((env ENV)) Bool 
    (=> (A_ENV env) (G_ENV env))
)

; State estimator
(declare-sort SE 0)
; Input \xi
(declare-fun SE_xi (SE) Trj)
; Output estimate \hat{s}
(declare-fun SE_shat (SE) Trj)
; Assumptions
; - The state estimator makes no assumptions
(define-fun A_SE ((se SE)) Bool
    true
)
; Guarantees
; - The estimate is close to the real state
(define-fun G_SE ((se SE)) Bool
  (forall ((t Real)) 
    (InBall (poseAt (SE_shat se) t) (poseAt (SE_xi se) t)  delta ) 
  )
)
; Saturated guarantee
(define-fun Gnf_SE ((se SE)) Bool 
    (=> (A_SE se) (G_SE se))
)

; Top level TES component
(declare-sort TES 0)
; Input trajectory trj
(declare-fun TES_trj (TES) Trj)
; Output state of the environment \xi
(declare-fun TES_xi (TES) Trj)
; Output of the internal state estimate \hat{s}
(declare-fun TES_shat (TES) Trj)
; Assumptions
; - The trajectory start at the state estimate 
(define-fun A_TES ((tes TES)) Bool
    (= (poseAt (TES_shat tes) 0) (poseAt (TES_trj tes) 0))
)
; Guarantees
; - The environment follows the given trajectory
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
; Subcomponents:
; The trajectory follower
(declare-fun TES_tf (TES) TF)
; The environment
(declare-fun TES_env (TES) ENV)
; The state estimator
(declare-fun TES_se (TES) SE)

; System instance
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
; Check that the assumptions of the trajectory follower are satisfied
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
; Check that the top-level requirements are satisfied
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
