; Pose datatype
(declare-sort Pose 0)
(declare-fun Pose_x (Pose) Real)
(declare-fun Pose_y (Pose) Real)
(declare-fun Pose_theta (Pose) Real)

;;;; ROADMAPS
; Node type
(declare-sort Node 0)
; Node label type 
(declare-datatypes () ((NodeLabel g t c h)))
; Node labelling function
(declare-fun lbl (Node) NodeLabel)
; Pose associated with a node
(declare-fun loc (Node) Pose)
; Link type
(declare-sort Link 0)
; Length of a link
(declare-fun len (Link) Real)
; Source of a link
(declare-fun src (Link) Node)
; Destination of a link
(declare-fun dst (Link) Node)
; Roadmap type
(declare-sort Roadmap 0)
; Test if a node is in the roadmap
(declare-fun InN (Node Roadmap) Bool)
; Test if a link is in the roadmap
(declare-fun InL (Link Roadmap) Bool)
; Uninterpreted predicate for the validity of a roadmap
; (to be defined using "assert" statements)
(declare-fun ValidRm (Roadmap) Bool)

; Route type
(declare-sort Route 0)
; Number of links in a route
(declare-fun length (Route) Int)
; Selection of the i-th link
(declare-fun linkAt (Route Int) Link)
; Distance function from the start of the route to the 
; destination of the i-th link
(declare-fun d (Route Int) Real)
(assert 
    (forall ((rt Route))
        (and 
            (= (d rt 0) 0.0)
            (forall ((i Int))
                (=> 
                    (and (>= i 1) (<= i  (length rt)) ) 
                    (= (d rt i) (+ (d rt (- i 1)) (len (linkAt rt i)) ))
                )
            )
        )
    )
)

; Trajectory type
(declare-sort Trj 0)
; Pose along the trajectory from the initial node to a given distance
(declare-fun poseAt (Trj Real) Pose)
; Total length of a trajectory
(declare-fun Trj_length (Trj) Real)
; Motion primitive associated with a link 
; (given a link and a distance, this function defines the pose)
(declare-fun pr (Link Real) Pose)
; Predicate that is true if a route rt is a valid route from start to end in a roadmap
(define-fun InRts ((rm Roadmap)(start Node)(end Node)(rt Route)) Bool
        (and 
            ; the source of the first link must be start
            (= (src (linkAt rt 1)) start)
            ; the destination of the last link must be end
            (= (dst (linkAt rt (length rt) )) end)
            ; all links must be adjacient
            (forall ((i Int)) 
                (=>
                    (and (>= i 1) (<= i (- (length rt) 1)))
                    (=  (dst (linkAt rt i)) (src (linkAt rt (+ i 1)))  )    
                ) 
            )
            ; all links must be in the roadmap
            (forall ((i Int)) 
                (=>
                    (and (>= i 1) (<= i (length rt)))
                    (InL (linkAt rt i) rm)   
                ) 
            )
        )
)

; Predicate that is true if a trajectory trj is a valid trajectory from start to end in a roadmap
(define-fun InTrjs ((rm Roadmap)(start Node)(end Node)(trj Trj)) Bool
    ; it must be the trajectory associated with some valid route
    (exists ((rt Route))
        (and 
            (InRts rm start end rt)
            ; It must follow the motion primitives associted with each link
            (forall((i Int))
                (=>
                    (and (>= i 1) (<= i (length rt) ))
                    (forall ((p Real))
                        (=> (and (>= p (d rt (- i 1))) (<= p (d rt i )) )
                            (= 
                                (poseAt trj p)
                                (pr (linkAt rt i) (- p (d rt (- i 1))) )   
                            )
                        )
                    )
                )  
            )
            ; Total length must match the total lenght of the route
            (= (Trj_length trj) (d rt (length rt)))   
        )
    )
)

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

; Existance of a route in a roadmap 
(declare-fun ExistsRt (Roadmap Node Node) Bool)

; Link between time and distance (in reality, this is an integral of the velocity function)
; we only need this to move from time to distance but its definition is not really needed 
; in the proofs.
(declare-fun intg (Real) Real)

;;;;;  COMPONENTS

; Route generator component definition
(declare-sort RG 0)
; Input to
(declare-fun RG_to (RG) Node)
; Output rt
(declare-fun RG_rt (RG) Route)
; Input \hat{n}
(declare-fun RG_nhat (RG) Node)
; Input rm 
(declare-fun RG_rm (RG) Roadmap)
; Assumption: 
; - the roadmap must be valid, 
; - the start and end nodes must be in the roadmap
; - there must be a path that connects start and end
(define-fun A_RG ((rg RG)) Bool
    (and 
        (ValidRm (RG_rm rg)) 
        (InN (RG_to rg) (RG_rm rg)) (InN (RG_nhat rg) (RG_rm rg))
        (ExistsRt (RG_rm rg) (RG_nhat rg) (RG_to rg)) 
    )
)
; Guarantee:
; - The output route is a valid route from \hat{n} to to
(define-fun G_RG ((rg RG)) Bool
    (InRts (RG_rm rg) (RG_nhat rg) (RG_to rg) (RG_rt rg))
)
; Saturated guarantee
(define-fun Gnf_RG ((rg RG)) Bool 
    (=> (A_RG rg) (G_RG rg))
)

; TTES component definition 
(declare-sort TTES 0)
; Input rt
(declare-fun TTES_rt (TTES) Route)
; Input \hat{n}
(declare-fun TTES_nhat (TTES) Node)
; Output \xi
(declare-fun TTES_xi (TTES) Trj)
; Input rm
(declare-fun TTES_rm (TTES) Roadmap)
; Assumption
; - The assigned route first node must be the initial node estimate \hat{n}
; - The route must be a sequence of adjiacient links (looser than the guarantee of RG)
(define-fun A_TTES ((ttes TTES)) Bool
    (and 
        (= (src (linkAt (TTES_rt ttes) 1)) (TTES_nhat ttes))
        (forall ((i Int)) 
            (=>
                (and (>= i 1) (<= i (- (length (TTES_rt ttes)) 1)))
                (= (dst (linkAt (TTES_rt ttes) i)) (src (linkAt (TTES_rt ttes) (+ i 1))))   
            ) 
        )
    )
)
; Any positive error would do
(declare-const delta  Real)
(assert (>= delta 0))
; Guarantee
; - The TTES system will follow a valid trajectory within some error bound
(define-fun G_TTES ((ttes TTES)) Bool
    (exists ((trj Trj))
        (and
            (InTrjs (TTES_rm ttes) (TTES_nhat ttes) (dst (linkAt (TTES_rt ttes) (length (TTES_rt ttes))) ) trj)
            (forall ((p Real))
                (=> (and (>= p 0) (<= p (Trj_length trj))) 
                    (exists ((t Real))
                        (and
                            (= p (intg t))
                            (InBall (poseAt (TTES_xi ttes) t) (poseAt trj p) delta)
                        ) 
                    )
                )
            )
        )
    )
)
; Saturated guarantee
(define-fun Gnf_TTES ((ttes TTES)) Bool 
    (=> (A_TTES ttes) (G_TTES ttes))
)

; Top level system type
(declare-sort AutoTaxi 0)
; TTES sub-component
(declare-fun AutoTaxi_ttes (AutoTaxi) TTES)
; Route generator sub-component
(declare-fun AutoTaxi_rg (AutoTaxi) RG)
; Input to
(declare-fun AutoTaxi_to (AutoTaxi) Node)
; Output xi
(declare-fun AutoTaxi_xi (AutoTaxi) Trj)
; Output \hat{n}
(declare-fun AutoTaxi_nhat (AutoTaxi) Node)
; Input rm
(declare-fun AutoTaxi_rm (AutoTaxi) Roadmap)
; Specififcaiton assumption
(define-fun AutoTaxi_A ((at AutoTaxi)) Bool 
     (and 
        (ValidRm (AutoTaxi_rm at)) 
        (InN (AutoTaxi_to at) (AutoTaxi_rm at)) (InN (AutoTaxi_nhat at) (AutoTaxi_rm at))
        (ExistsRt (AutoTaxi_rm at) (AutoTaxi_nhat at) (AutoTaxi_to at)) 
    )
)
; Specification guarantee
(define-fun AutoTaxi_G ((at AutoTaxi)) Bool
    (exists ((trj Trj))
        (and
            (InTrjs (AutoTaxi_rm at) (AutoTaxi_nhat at) (AutoTaxi_to at) trj)
            (forall ((p Real))
                (=> (and (>= p 0) (<= p (Trj_length trj) )) 
                    (exists ((t Real))
                        (and
                            (= p (intg t))
                            (InBall (poseAt (AutoTaxi_xi at) t) (poseAt trj p) delta)
                        ) 
                    )
                )
            )
        )
    )
)

; Definition of an instance of the autonomous taxi system
(declare-const autotaxi AutoTaxi)

; Connections among components
(assert 
    (and
        (= (AutoTaxi_to autotaxi) (RG_to (AutoTaxi_rg autotaxi)))
        (= (AutoTaxi_xi autotaxi) (TTES_xi (AutoTaxi_ttes autotaxi)))
        (= (AutoTaxi_xi autotaxi) (TTES_xi (AutoTaxi_ttes autotaxi)))
        (= (AutoTaxi_nhat autotaxi) (TTES_nhat (AutoTaxi_ttes autotaxi)))
        (= (AutoTaxi_rm autotaxi) (TTES_rm (AutoTaxi_ttes autotaxi)))
        (= (AutoTaxi_nhat autotaxi) (RG_nhat (AutoTaxi_rg autotaxi)))
        (= (AutoTaxi_rm autotaxi) (RG_rm (AutoTaxi_rg autotaxi)))
        (= (RG_rt (AutoTaxi_rg autotaxi)) (TTES_rt (AutoTaxi_ttes autotaxi)) )
    )
)

; Verification that the top level requirements are satisfied
(push)
(assert 
    (not
        (=>
            (and
                (AutoTaxi_A autotaxi)
                (Gnf_RG (AutoTaxi_rg autotaxi))
                (Gnf_TTES (AutoTaxi_ttes autotaxi))
            )
            (AutoTaxi_G autotaxi)
        )
    )
)
(check-sat)
(pop)
(push)
; Verification that the assumption of TTES are satisfied
(assert 
    (not
        (=>
            (and
                (AutoTaxi_A autotaxi)
                (Gnf_RG (AutoTaxi_rg autotaxi))
            )
            (A_TTES (AutoTaxi_ttes autotaxi))
        )
    )
)
(check-sat)
(pop)
(push)
; Verification that the assumption of RG are satisfied
(assert 
    (not
        (=>
            (and
                (AutoTaxi_A autotaxi)
                (Gnf_TTES (AutoTaxi_ttes autotaxi))
            )
            (A_RG (AutoTaxi_rg autotaxi))
        )
    )
)
(check-sat)
(pop)












