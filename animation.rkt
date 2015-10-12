;; Dylan Richardson

#| Project Report
  In order to run an animation you must execute "(run-animation animation-name)".
The example animations in this file are:
ANIMATION1, ANIMATION2, ANIMATION3, CUSTOM - required
BOUNCE - demonstrates a bug in the program that I could not figure out how to fix
  All of the required commands are fully functional in this program. Every
command that updates a graphic is able to take a list of graphics and apply
the operation to each element in the list. The graphic variable supports all
kinds of images which includes circles and rectangles. The position, velocity,
and acceleration (indirectly through the move command) of graphics are definable
by the programmer. Repetition and conditional commands are also available to
programmer.
  There were four changes made to the design of the language. The width and
height parameters for an animation were removed, because all of the animations
are the same size so there is no need for this option. The second change was
adding an extra argument called "shape" to the graphic structure. This change
was made to improve collision detection. Before, every object collided like a
rectangle. This addition lets graphics with "'circle" as its shape to detect a
collision and bounce like a circle. The next change made was adding lower and
upper bound arguments to the jump command. I made this change because ANIMATION2
was ending too quickly. To rememdy this I made it so the purple circle would
only jump between (50,50) and (550,350) instead of (0,0) and (600,400). The last
change was limiting the bounce command to only accept two graphics as arguments
instead of two lists of graphics. It makes more sense to have two objects
colliding and bouncing with each other than two lists of graphics all colliding
at the same time.
  The biggest problem I have with my language and interpreter is that it is
somewhere between a linear, predictable animation and a physics based
simulation. Because of this, the program is very comlicated for an interpreter
while it would have made more sense to have written the language in an event
driven system. One poor deisgn decision was making most of the functions in the
interpreter return void. This made it impossible to have test cases for these
functions. Another problem that I have with my program is with the macros. Many
of the macros allow for the removal of parantheses around a list of elements if
there is only one element in the list. This feature does not work if the one
element is defined inline. For example, the code "(Loop cmd1 Until col1)" works
fine, but if you try to replace col1 with its definition like "(Loop cmd1 Until
(Collision obj1 obj2))" an error is thrown because the macro matches Collision,
obj1, and obj2 to three different collisions. Lastly, if I had more time I would
have liked to implement a macro called "Simulation" that takes a list of graphics
and expands into an animation that moves and bounces each object accordingly.|#

(require "world-cs1102.rkt")
(require "images.rkt")
(require test-engine/racket-gui)
(require (for-syntax scheme/base))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; THE LANGUAGE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; a program in this language is an animation

;; an animation is (make-animation list-of-vargraphic list-of-cmd)
(define-struct animation (objects cmds))

;; a list-of-cmd is either
;;   - empty, or
;;   - (cons cmd list-of-cmd)

;; a cmd is either
;;   - cmd-loop-until,
;;   - cmd-if,
;;   - move,
;;   - jump,
;;   - insertion,
;;   - removal,
;;   - bounce,or
;;   - graphic-change

;; a cmd-loop-until is (make-cmd-loop-until list-of-collision-cond list-of-cmd)
(define-struct cmd-loop-until (tests cmds))

;; a cmd-if is (make-cmd-if list-of-collision-cond list-of-cmd)
(define-struct cmd-if (tests cmds))

;; a graphic is (make-graphic image posn velocity symbol)
;; shape can be 'circle or 'rectangle
(define-struct graphic (pic pos vel shape))

;; a velocity is (make-velocity number number)
(define-struct velocity (x y))

;; an acceleration is (make-acceleration number number)
(define-struct acceleration (x y))

;; a vargraphic is (make-vargraphic graphic symbol)
(define-struct vargraphic (object varname))

;; a collision-cond is (make-collision-cond list-of-symbol list-of-symbol)
(define-struct collision-cond (objects1 objects2))

;; a edge-collision-cond is (make-collision-cond list-of-symbol list-of-symbol)
(define-struct edge-collision-cond (objects sides))

;; a move is (make-move list-of-symbol acceleration)
(define-struct move (objects accel))

;; a jump is (make-jump list-of-symbol posn posn)
(define-struct jump (objects lower upper))

;; an insertion is (make-insertion list-of-vargraphic)
(define-struct insertion (objects))

;; a removal is (make-removal list-of-symbol)
(define-struct removal (objects))

;; a bounce is (make-bounce symbol symbol)
(define-struct bounce (object1 object2))

;; a graphic-change is (make-graphic-change list-of-symbol value)
(define-struct graphic-change (objects val))

;;;;;;;;;;; HELPERS ;;;;;;;;;;;

;; rand-velocity : number number -> velocity
;; consumes two numbers
;; produces a random velocity with magnitude between the two numbers
(define (rand-velocity lower upper)
     (let* [(x (- (* 2 (random) upper) upper))
            (y (+ (* (random) (- (sqrt (- (* upper upper) (* x x)))
                                 (sqrt (max 0 (- (* lower lower) (* x x))))))
                  (sqrt (max 0 (- (* lower lower) (* x x))))))]
     (make-velocity x y)))

;;;;;;;;;;; MACROS ;;;;;;;;;;;

;; Wraps local around the definitions, makes vargraphics out of the
;;   variables, and wraps list around the vargraphics and commands
(define-syntax Animation
  (syntax-rules (Variables Commands Definitions : =)
    [(Animation Definitions : [(name1 = val1) ...] Variables : [(name2 = val2) ...] Commands : [cmd1 ...])
     (local [(define name1 val1) ...] (make-animation (list (Var name2 = val2) ...) (list cmd1 ...)))]
    [(Animation Definitions : [(name1 = val1) ...] Commands : [cmd1 ...] Variables : [(name2 = val2) ...])
     (local [(define name1 val1) ...] (make-animation (list (Var name2 = val2) ...) (list cmd1 ...)))]
    [(Animation Variables : [(name2 = val2) ...] Definitions : [(name1 = val1) ...] Commands : [cmd1 ...])
     (local [(define name1 val1) ...] (make-animation (list (Var name2 = val2) ...) (list cmd1 ...)))]
    [(Animation Variables : [(name2 = val2) ...] Commands : [cmd1 ...] Definitions : [(name1 = val1) ...])
     (local [(define name1 val1) ...] (make-animation (list (Var name2 = val2) ...) (list cmd1 ...)))]
    [(Animation Commands : [cmd1 ...] Definitions : [(name1 = val1) ...] Variables : [(name2 = val2) ...])
     (local [(define name1 val1) ...] (make-animation (list (Var name2 = val2) ...) (list cmd1 ...)))]
    [(Animation Commands : [cmd1 ...] Variables : [(name2 = val2) ...] Definitions : [(name1 = val1) ...])
     (local [(define name1 val1) ...] (make-animation (list (Var name2 = val2) ...) (list cmd1 ...)))]
    [(Animation Variables : [(name2 = val2) ...] Commands : [cmd1 ...])
     (make-animation (list (Var name2 = val2) ...) (list cmd1 ...))]
    [(Animation Commands : [cmd1 ...] Variables : [(name2 = val2) ...])
     (make-animation (list (Var name2 = val2) ...) (list cmd1 ...))]))

;; Avoids language structures ("make-...")
(define-syntax Vargraphic
  (syntax-rules ()
    [(Vargraphic image (x y) (vx vy) shape name)
     (make-vargraphic
      (make-graphic image
                    (make-posn x y)
                    (make-velocity vx vy)
                    'shape) 'name)]
    [(Vargraphic image (x y) (RandomVelocity lower upper) shape name)
     (cond [(> lower upper)
            (error (format "Lower magnitude is greater than upper: ~a > ~a" lower upper))]
           [(< lower 0)
            (error (format "Lower magnitude is less than zero: ~a" lower))]
           [(< upper 0)
            (error (format "Upper magnitude is less than zero: ~a" upper))]
           [else (make-vargraphic
                  (make-graphic image
                                (make-posn x y)
                                (RandomVelocity lower upper)
                                'shape) 'name)])]))

;; Error checks random-velocity function
(define-syntax RandomVelocity
  (syntax-rules ()
    [(RandomVelocity lower upper)
     (cond [(> lower upper)
            (error (format "Lower magnitude is greater than upper: ~a > ~a" lower upper))]
           [(< lower 0)
            (error (format "Lower magnitude is less than zero: ~a" lower))]
           [(< upper 0)
            (error (format "Upper magnitude is less than zero: ~a" upper))]
           [else (rand-velocity lower upper)])]))

;; Implicitly defines the shape of a vargraphic based on the image
(define-syntax Var
  (syntax-rules (Circle Rectangle =)
    [(Var name = ((Circle radius color) pos vel))
     (Vargraphic (Circle radius color) pos vel circle name)]
    [(Var name = ((Rectangle w h color) pos vel))
     (Vargraphic (Rectangle w h color) pos vel rectangle name)]
    [(Var name = (image pos vel))
     (Vargraphic image pos vel rectangle name)]
    [(Var name = (image pos vel shape))
     (Vargraphic image pos vel shape name)]))

;; Error checks the circle function and removes the mode field
(define-syntax Circle
  (syntax-rules ()
    [(Circle radius color)
     (cond [(< radius 0) (error (format "Circle radius must be non-negative: ~a" radius))]
           [(not (symbol? 'color)) (error (format "Circle color must be a symbol ~a" color))]
           [else (circle radius "solid" 'color)])]))

;; Error checks the rectangle function and removes the mode field
(define-syntax Rectangle
  (syntax-rules ()
    [(Rectangle w h color)
     (cond [(< w 0) (error (format "Rectangle width must be non-negative: ~a" w))]
           [(< h 0) (error (format "Rectangle height must be non-negative: ~a" h))]
           [(not (symbol? 'color)) (error (format "Rectangle color must be a symbol ~a" color))]
           [else (rectangle w h "solid" 'color)])]))

;; Creates a vargraphic that represents the top edge of the frame
(define-syntax TopEdge
  (syntax-rules ()
    [(TopEdge)
     (Vargraphic (Rectangle 800 100 white) (300 -50) (0 0) 'rectangle 'TopEdge)]))

;; Creates a vargraphic that represents the bottom edge of the frame
(define-syntax BottomEdge
  (syntax-rules ()
    [(BottomEdge)
     (Vargraphic (Rectangle 800 100 white) (300 450) (0 0) 'rectangle 'BottomEdge)]))

;; Creates a vargraphic that represents the left edge of the frame
(define-syntax LeftEdge
  (syntax-rules ()
    [(LeftEdge)
     (Vargraphic (Rectangle 100 600 white) (-50 200) (0 0) 'rectangle 'LeftEdge)]))

;; Creates a vargraphic that represents the right edge of the frame
(define-syntax RightEdge
  (syntax-rules ()
    [(RightEdge)
     (Vargraphic (Rectangle 100 600 white) (650 200) (0 0) 'rectangle 'RightEdge)]))

;; Wraps list around the objects and sets the acceleration to (0,0)
(define-syntax Move
  (syntax-rules ()
    [(Move obj1 ...)
     (make-move (list 'obj1 ...) (make-acceleration 0 0))]))

;; Wraps list around the objects and sets the acceleration to (ax,ay)
(define-syntax Accel
  (syntax-rules ()
    [(Accel (ax ay) obj1 ...)
     (make-move (list 'obj1 ...) (make-acceleration ax ay))]))

;; Wraps list around the objects and sets the lower and upper bounds to (0,0)
;;   and (600 400) or the points specified
(define-syntax Jump
  (syntax-rules ()
    [(Jump (x1 y1) (x2 y2) obj1 ...)
     (make-jump (list 'obj1 ...) (make-posn x1 y1) (make-posn x2 y2))]
    [(Jump obj1 ...)
     (make-jump (list 'obj1 ...) (make-posn 0 0) (make-posn 600 400))]))

;; Adds quotes to the objects and the syntax follows the other macros
(define-syntax Bounce
  (syntax-rules ()
    [(Bounce obj1 obj2)
     (make-bounce 'obj1 'obj2)]))

;; Wraps list around the objects
(define-syntax Insert
  (syntax-rules ()
    [(Insert obj1 ...)
     (make-insertion (list obj1 ...))]))

;; Wraps list around the objects
(define-syntax Remove
  (syntax-rules ()
    [(Remove obj1 ...)
     (make-removal (list 'obj1 ...))]))

;; Wraps list around the names and avoids language structures
(define-syntax Change
  (syntax-rules (velocity position image)
    [(Change velocity (vx vy) name1 ...)
     (make-graphic-change (list 'name1 ...) (make-velocity vx vy))]
    [(Change position (x y) name1 ...)
     (make-graphic-change (list 'name1 ...) (make-posn x y))]
    [(Change image pic name1 ...)
     (make-graphic-change (list 'name1 ...) pic)]))

;; Wraps lists around the objects and allows for the removal of parentheses
;;   around a list of one object
(define-syntax Collision
  (syntax-rules ()
    [(Collision (obj1 ...) (obj2 ...))
     (make-collision-cond (list 'obj1 ...) (list 'obj2 ...))]
    [(Collision (obj1 ...) obj2)
     (make-collision-cond (list 'obj1 ...) (list 'obj2))]
    [(Collision obj1 (obj2 ...))
     (make-collision-cond (list 'obj1) (list 'obj2 ...))]
    [(Collision obj1 obj2)
     (make-collision-cond (list 'obj1) (list 'obj2))]))

;; Wraps lists around the objects and allows for the removal of parentheses
;;   around a list of one object
(define-syntax EdgeCollision
  (syntax-rules ()
    [(EdgeCollision (obj1 ...) (side1 ...))
     (EdgeCollisionl (list 'obj1 ...) (list 'side1 ...))]
    [(EdgeCollision (obj1 ...) side1)
     (EdgeCollisionl (list 'obj1 ...) (list 'side1))]
    [(EdgeCollision obj1 (side1 ...))
     (EdgeCollisionl (list 'obj1) (list 'side1 ...))]
    [(EdgeCollision obj1 side1)
     (EdgeCollisionl (list 'obj1) (list 'side1))]))

;; Error checks the sides
(define-syntax EdgeCollisionl
  (syntax-rules ()
    [(EdgeCollisionl objs sides)
     (begin
       (for-each (λ (side)
           (if (member side (list 'top 'bottom 'left 'right 'any)) true
               (error (format "Edge does not exist: ~a" side)))) sides)
       (cond [(member 'any sides)
              (make-edge-collision-cond objs (list 'top 'bottom 'left 'right))]
             [else (make-edge-collision-cond objs sides)]))]))

;; Wraps lists around the objects and allows for the removal of parentheses
;;   around a list of one object
(define-syntax Loop
  (syntax-rules (Until)
    [(Loop (cmd1 ...) Until (col1 ...))
     (make-cmd-loop-until (list col1 ...) (list cmd1 ...))]
    [(Loop (cmd1 ...) Until col1)
     (make-cmd-loop-until (list col1) (list cmd1 ...))]
    [(Loop cmd1 Until (col1 ...))
     (make-cmd-loop-until (list col1 ...) (list cmd1))]
    [(Loop cmd1 Until col1)
     (make-cmd-loop-until (list col1) (list cmd1))]))

;; Wraps lists around the objects and allows for the removal of parentheses
;;   around a list of one object
(define-syntax If
  (syntax-rules ()
    [(If (col1 ...) (cmd1 ...))
     (make-cmd-if (list col1 ...) (list cmd1 ...))]
    [(If (col1 ...) cmd1)
     (make-cmd-if (list col1 ...) (list cmd1))]
    [(If col1 (cmd1 ...))
     (make-cmd-if (list col1) (list cmd1 ...))]
    [(If col1 cmd1)
     (make-cmd-if (list col1) (list cmd1))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; EXAMPLES ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ANIMATION1
  (Animation
   Definitions : [(redCircleMove = (Move redCircle))]
   Variables   : [(redCircle = ((Circle 30 red) (120 100) (5 1)))
                  (blueRectangle = ((Rectangle 60 320 blue) (480 200) (0 0)))]
   Commands    : [(Loop redCircleMove Until ((Collision redCircle blueRectangle)))
                  (Bounce redCircle blueRectangle)
                  (Remove blueRectangle)
                  (Loop redCircleMove Until ((EdgeCollision redCircle left)))]))

(define ANIMATION2
  (Animation
   Variables : [(purpleCircle = ((Circle 60 purple) (510 320) (0 0)))]
   Commands  : [(Loop ((Jump (50 50) (550 350) purpleCircle))
                 Until ((EdgeCollision purpleCircle any)))]))

(define ANIMATION3
  (Animation
   Definitions : [(orangeCircleMove = (Move orangeCircle))]
   Variables :   [(orangeCircle = ((Circle 30 orange) (150 100) (0 5)))
                  (greenRectangle = ((Rectangle 420 40 green) (300 340) (0 0)))]
   Commands  :   [(Loop orangeCircleMove Until ((Collision orangeCircle greenRectangle)))
                  (Change velocity (5 0) orangeCircle)
                  (Insert (Var redRectangle = ((Rectangle 40 260 red) (420 160) (0 0))))
                  (Loop orangeCircleMove Until ((Collision orangeCircle redRectangle)))
                  (Jump (0 0) (600 400) orangeCircle)]))

;; This is an animation that has two circles moving in the same direction
;;   with different speeds. They should bounce in different directions but
;;   they do not which is a bug in the function calc-rbvel.
(define BOUNCE
  (Animation
   Definitions : [(move = (Move red blue))]
   Variables   : [(red = ((Circle 50 red) (300 250) (0 0.5)))
                  (blue = ((Circle 50 blue) (300 100) (0 2)))]
   Commands    : [(Loop move Until ((Collision red blue)))
                  (Bounce red blue)
                  (Loop move Until ((EdgeCollision (red blue) any)))]))


;; This is an animation that has a soccer ball and basketball with two random
;;   velocities. When they bounce off a wall the color of the ball changes to
;;   the color of the wall. The animation ends when either the soccer ball
;;   hits yellow wall or the basketball hits the green wall.
(define CUSTOM
  (Animation
   Definitions : []
   Variables   : [(soccer = ((overlay (circle 49 "solid" "white") soccerPic)
                             (400 133) (RandomVelocity 1 2) rectangle))
                  (bball = ((overlay (circle 50 "solid" "white") bballPic)
                            (200 266) (RandomVelocity 1 2) rectangle))
                  (redRectangle = ((Rectangle 600 40 red) (300 0) (0 0)))
                  (blueRectangle = ((Rectangle 600 40 blue) (300 400) (0 0)))
                  (yellowRectangle = ((Rectangle 40 400 yellow) (0 200) (0 0)))
                  (greenRectangle = ((Rectangle 40 400 green) (600 200) (0 0)))]
   Commands    : [(Loop ((Loop ((Accel (0.2 0) soccer) (Accel (-0.2 0) bball))
                          Until ((Collision (soccer bball)
                                 (redRectangle blueRectangle yellowRectangle greenRectangle soccer bball))))
                         (If ((Collision soccer redRectangle))
                             ((Change image (overlay (circle 49 "solid" "red") soccerPic) soccer)
                              (Bounce soccer redRectangle)))
                         (If ((Collision bball redRectangle))
                             ((Change image (overlay (circle 50 "solid" "red") bballPic) bball)
                              (Bounce bball redRectangle)))
                         (If ((Collision soccer blueRectangle))
                             ((Change image (overlay (circle 49 "solid" "blue") soccerPic) soccer)
                              (Bounce soccer blueRectangle)))
                         (If ((Collision bball blueRectangle))
                             ((Change image (overlay (circle 50 "solid" "blue") bballPic) bball)
                              (Bounce bball blueRectangle)))
                         (If ((Collision bball yellowRectangle))
                             ((Change image (overlay (circle 50 "solid" "yellow") bballPic) bball)
                              (Bounce bball yellowRectangle)))
                         (If ((Collision soccer greenRectangle))
                             ((Change image (overlay (circle 49 "solid" "green") soccerPic) soccer)
                              (Bounce soccer greenRectangle)))
                         (If ((Collision soccer bball))
                             ((Change image (overlay (circle 49 "solid" "white") soccerPic) soccer)
                              (Change image (overlay (circle 50 "solid" "white") bballPic) bball)
                              (Bounce soccer bball)))
                         (Accel (0.2 0) soccer) (Accel (-0.2 0) bball))
                   Until ((Collision soccer yellowRectangle) (Collision bball greenRectangle)))
                  (If ((Collision soccer yellowRectangle))
                      ((Change image (overlay (circle 49 "solid" "yellow") soccerPic) soccer)
                       (λ () (println "The soccer ball won"))))
                  (If ((Collision bball greenRectangle))
                      ((Change image (overlay (circle 50 "solid" "green") bballPic) bball)
                       (λ () (println "The basketball won"))))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; INTERPRETER ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;; VARIABLES ;;;;;;;;;

;; A var is (make-var symbol graphic)
(define-struct var (name val))

;; a list-of-var is either
;;   - empty, or
;;   - (cons var list-of-var)

;; vars is a list-of-var
(define vars empty)

;; clear-vars : -> void
;; empties the vars list
(define (clear-vars)
  (set! vars empty))

;; lookup-var : symbol -> graphic
;; produces graphic associated with given variable name
(define (lookup-var varname)
  (let ([varstructs (filter (lambda (avar) (symbol=? varname (var-name avar))) vars)])
    (cond [(cons? varstructs) (var-val (first varstructs))]
          [else (error 'lookup-var (format "variable ~a not defined" varname))])))

;; update-var : symbol graphic -> void
;; change value of named var to given graphic
(define (update-var varname newval)
  (set! vars 
        (map (λ (avar) 
               (cond [(symbol=? varname (var-name avar)) (make-var varname newval)]
                     [else avar]))
             vars)))

;;;;;;; ANIMATION LOGIC ;;;;;;

;; run-animation : animation -> void
;; executes the commands in an animation
(define (run-animation anim)
    (clear-vars)
    (insert-graphics (animation-objects anim))
    (big-bang 600 400 1/28 true)
    (update-frame (rectangle 600 400 "solid" "white"))
    (run-cmdlist (animation-cmds anim)))

;; run-cmdlist : list-of-cmd -> void
;; executes every command in a list
(define (run-cmdlist cmd-lst)
  (for-each run-cmd cmd-lst))

;; run-cmd : cmd -> void
;; executes the given command and draws the world after
;;   every one except bounce then sleeps
(define (run-cmd cmd)
  (cond [(bounce? cmd)
         (bounce-graphics (bounce-object1 cmd) (bounce-object2 cmd))]
        [else 
         (cond [(cmd-loop-until? cmd)
                (until (cmd-loop-until-tests cmd) (cmd-loop-until-cmds cmd))]
               [(cmd-if? cmd)
                (cond [(collision-in-conds? (cmd-if-tests cmd))
                       (run-cmdlist (cmd-if-cmds cmd))]
                      [else (void)])]
               [(move? cmd)
                (move-graphics (move-objects cmd) (move-accel cmd))]
               [(jump? cmd)
                (jump-graphics (jump-objects cmd) (jump-lower cmd) (jump-upper cmd))
                (sleep/yield 0.1)]
               [(insertion? cmd)
                (insert-graphics (insertion-objects cmd))]
               [(removal? cmd)
                (remove-graphics (removal-objects cmd))]
               [(graphic-change? cmd)
                (change-graphics (graphic-change-objects cmd) (graphic-change-val cmd))]
               [else (cmd)])
         (draw-world)
         (sleep/yield 0.0001)]))

;; until : list-of-collision-cond list-of-cmd -> void
;; runs the list of commands until any of the
;;   collision conditions return true
(define (until tests cmds)
  (cond [(collision-in-conds? tests) (void)]
        [else (run-cmdlist cmds) (until tests cmds)]))

;; move-graphics : list-of-symbol -> void
;; consumes a list of variable names
;; changes the graphics to have new positions and velocities
(define (move-graphics names accel)
  (for-each (λ (name) (move-graphic name accel)) names))

;; move-graphic : symbol -> void
;; consumes a variable name
;; changes the graphic to have a new position and velocity
(define (move-graphic name accel)
  (let [(v (lookup-var name))]
    (update-var name
                (make-graphic
                 (graphic-pic v)
                 (make-posn
                  (+ (posn-x (graphic-pos v)) (velocity-x (graphic-vel v)))
                  (+ (posn-y (graphic-pos v)) (velocity-y (graphic-vel v))))
                 (make-velocity
                  (+ (velocity-x (graphic-vel v)) (acceleration-x accel))
                  (+ (velocity-y (graphic-vel v)) (acceleration-y accel)))
                 (graphic-shape v)))))

;; jump-graphics : list-of-symbol posn posn -> void
;; consumes a list of variable names and a lower and upper bound
;; changes the graphics to have random positions within the bounds
(define (jump-graphics names lower upper)
  (for-each (λ (name) (jump-graphic name lower upper)) names))

;; jump-graphic : symbol posn posn -> void
;; consumes a variable name and a lower and upper bound
;; changes the graphic to have a random position within the bounds
(define (jump-graphic name lower upper)
  (let [(v (lookup-var name))]
    (update-var name
                (make-graphic
                 (graphic-pic v)
                 (make-posn
                  (+ (* (random) (- (posn-x upper) (posn-x lower))) (posn-x lower))
                  (+ (* (random) (- (posn-y upper) (posn-y lower))) (posn-y lower)))
                 (graphic-vel v)
                 (graphic-shape v)))))

;; insert-graphics : list-of-vargraphic -> void
;; consumes a list of graphic variables
;; inserts the graphics into the list of variables
(define (insert-graphics objects) 
  (set! vars (append vars (map (λ (obj) (make-var (vargraphic-varname obj)
                                                  (vargraphic-object obj)))
                               objects))))

;; remove-graphics : list-of-symbol -> void
;; consumes a list of variable names
;; removes the graphics from the list of variables
(define (remove-graphics names)
  (set! vars (filter (λ (a-var)
                       (not (member (var-name a-var) names)))
                     vars)))

;; bounce-graphics : symbol symbol -> void
;; consumes a list of graphic variables
;; changes the graphics to have new velocities
(define (bounce-graphics name1 name2)
  (cond [(and (symbol=? 'circle (graphic-shape (lookup-var name1)))
              (symbol=? 'circle (graphic-shape (lookup-var name2))))
         (bounce-circles name1 name2)]
        [else (bounce-rects name1 name2)]))

;; bounce-rects : symbol symbol -> void
;; consumes two variable names
;; changes their velocities to relfect the rectangles bouncing off each other
(define (bounce-rects name1 name2)
  (update-vel name1 (calc-rbvel name1 name2))
  (update-vel name2 (calc-rbvel name2 name1)))

;; calc-rbvel : symbol symbol -> velocity
;; consumes two variable names
;; produces the velocity of the first rectangle bouncing off the second
(define (calc-rbvel name1 name2)
  (let* [(var1 (lookup-var name1))
         (var2 (lookup-var name2))
         (vx (velocity-x (graphic-vel var1)))
         (vy (velocity-y (graphic-vel var1)))]
    (cond [(or (= vx 0) (= vy 0))
           (make-velocity (* -1 vx) (* -1 vy))]
          [else
           (let [(x1 (posn-x (graphic-pos var1)))
                 (x2 (posn-x (graphic-pos var2)))
                 (y1 (posn-y (graphic-pos var1)))
                 (y2 (posn-y (graphic-pos var2)))
                 (w1 (/ (image-width (graphic-pic var1)) 2))
                 (w2 (/ (image-width (graphic-pic var2)) 2))
                 (h1 (/ (image-height (graphic-pic var1)) 2))
                 (h2 (/ (image-height (graphic-pic var2)) 2))
                 (a (sgn vy))
                 (b (sgn vx))]
             ;; check if horizontal or vertical collision
             (cond [(> (+ y1 (* a h1))
                       (+ (* (/ vy vx) (- (+ x1 (* b w1))
                                          (+ x2 (* -1 b w2))))
                          (+ y2 (* -1 a h2))))
                    (make-velocity (* -1 a vx) (* a vy))]
                   [else (make-velocity (* a vx) (* -1 a vy))]))])))

;; update-vel : symbol number number -> void
;; consumes a variable name and two numbers
;; changes the velocity of the graphic
(define (update-vel name vel)
  (let [(v (lookup-var name))]
    (update-var
     name (make-graphic (graphic-pic v) (graphic-pos v) vel (graphic-shape v)))))

;; bounce-circles : symbol symbol -> void
;; consumes two variable names
;; changes their velocities to relfect the circles bouncing off each other
(define (bounce-circles name1 name2)
  (update-vel name1 (calc-cbvel name1 name2))
  (update-vel name2 (calc-cbvel name2 name1)))

;; calc-cbvel : symbol symbol -> velocity
;; consumes two variable names
;; produces the velocity of the first circle bouncing off the second
;; I don't know how to calculate this so I'm just using a rectangular bounce
(define (calc-cbvel name1 name2)
  (calc-rbvel name1 name2))

;; change-graphics : list-of-symbol value -> void
;; consumes a list of variable names and a value
;; changes the variables to have the value in the correct field
(define (change-graphics names val)
  (for-each (λ (name) (change-graphic name val)) names))

;; change-graphic : symbol value -> void
;; consumes a variable name and a value
;; changes the variable to have the value in the correct field
(define (change-graphic name val)
  (let [(v (lookup-var name))]
    (update-var name
                (make-graphic
                 (if (image? val) val (graphic-pic v))
                 (if (posn? val) val (graphic-pos v))
                 (if (velocity? val) val (graphic-vel v))
                 (if (symbol? val) val (graphic-shape v))))))

;; collision-in-conds? : list-of-collision-cond -> boolean
;; determines if any of the collision conditions are true
(define (collision-in-conds? cols)
  (ormap collision-in-cond? cols))

;; collision-in-cond? : collision-cond -> boolean
;; determines if the collision condition is true
(define (collision-in-cond? col)
  (cond [(collision-cond? col)
         (or (ormap (λ (object)
                      (collision-in-list? object (collision-cond-objects2 col)))
                    (collision-cond-objects1 col))
             (ormap (λ (object)
                      (collision-in-list? object (collision-cond-objects1 col)))
                    (collision-cond-objects2 col)))]
        [(edge-collision-cond? col)
         (ormap (λ (object)
                  (collision-w-edges? object (edge-collision-cond-sides col)))
                (edge-collision-cond-objects col))]))

;; collision-w-edges? : symbol list-of-symbol -> boolean
;; determines if the graphic is colliding with any of the given edges
(define (collision-w-edges? name edges)
  (ormap (λ (edge) (collision-w-edge? name edge)) edges))

;; collision-w-edge? : symbol symbol -> boolean
;; determines if the graphic is colliding with the edge
(define (collision-w-edge? name edge)
  (let [(x (posn-x (graphic-pos (lookup-var name))))
        (y (posn-y (graphic-pos (lookup-var name))))
        (w (/ (image-width (graphic-pic (lookup-var name))) 2))
        (h (/ (image-height (graphic-pic (lookup-var name))) 2))]
    (cond [(symbol=? edge 'left) (<= (- x w) 0)]
          [(symbol=? edge 'right) (>= (+ x w) 600)]
          [(symbol=? edge 'top) (<= (- y h) 0)]
          [(symbol=? edge 'bottom) (>= (+ y h) 400)]
          [else (error (format "Edge does not exist: ~a" edge))])))

;; collision-in-list? : symbol list-of-symbol -> boolean
;; determines if there is a collision between one object and a list of objects
(define (collision-in-list? name1 names2)
  (ormap (λ (name2) (collision? name2 name1)) names2))

;; collision? : symbol symbol -> boolean
;; determines if the graphics are colliding
;; returns false if the two variable names are the same
(define (collision? name1 name2)
  (cond [(symbol=? name1 name2) false]
        [(and (symbol=? 'circle (graphic-shape (lookup-var name1)))
              (symbol=? 'circle (graphic-shape (lookup-var name2))))
         (circle-collision? name1 name2)]
        [else
         (rect-collision? name1 name2)]))

;; rect-collision? : symbol symbol -> boolean
;; determines if the two rectangles are colliding
(define (rect-collision? name1 name2)
  (let [(x1 (posn-x (graphic-pos (lookup-var name1))))
        (x2 (posn-x (graphic-pos (lookup-var name2))))
        (y1 (posn-y (graphic-pos (lookup-var name1))))
        (y2 (posn-y (graphic-pos (lookup-var name2))))
        (w1 (/ (image-width (graphic-pic (lookup-var name1))) 2))
        (w2 (/ (image-width (graphic-pic (lookup-var name2))) 2))
        (h1 (/ (image-height (graphic-pic (lookup-var name1))) 2))
        (h2 (/ (image-height (graphic-pic (lookup-var name2))) 2))]
    (and (<= (- x1 w1) (+ x2 w2))
         (>= (+ x1 w1) (- x2 w2))
         (<= (- y1 h1) (+ y2 h2))
         (>= (+ y1 h1) (- y2 h2)))))

;; circle-collision? : symbol symbol -> boolean
;; determines if two circles are colliding
(define (circle-collision? name1 name2)
  (let* [(x1 (posn-x (graphic-pos (lookup-var name1))))
         (x2 (posn-x (graphic-pos (lookup-var name2))))
         (y1 (posn-y (graphic-pos (lookup-var name1))))
         (y2 (posn-y (graphic-pos (lookup-var name2))))
         (r1 (/ (image-width (graphic-pic (lookup-var name1))) 2))
         (r2 (/ (image-width (graphic-pic (lookup-var name2))) 2))
         (dx (- x1 x2))
         (dy (- y1 y2))
         (tr (+ r1 r2))]
    (<= (+ (* dx dx) (* dy dy)) (* tr tr))))

;;;;;; INTERFACE HELPERS ;;;;;

;; draw-world : -> void
;; draws the scene 
(define (draw-world)
  (update-frame (draw-graphics vars)))

;; draw-graphics : list-of-var -> scene
;; consumes a list of variables
;; produces an image of all the graphics
(define (draw-graphics objects)
  (cond [(empty? objects) (empty-scene 600 400)]
        [(cons? objects)
         (place-image
          (graphic-pic (var-val (first objects)))
          (posn-x (graphic-pos (var-val (first objects))))
          (posn-y (graphic-pos (var-val (first objects))))
          (draw-graphics (rest objects)))]))

;;;;;;;;;; TEST CASES ;;;;;;;;

(define a (Var a = ((Circle 50 red) (100 100) (1 0))))
(define b (Var b = ((Circle 50 blue) (200 100) (-1 0))))
(define c (Var c = ((Rectangle 50 50 green) (300 300) (0 0))))
(define col1 (Collision a b))
(define col2 (Collision a c))
(define col3 (Collision b c))
(insert-graphics (list a b c))

;; I cannot test functions that return defined structures because the
;; check-expect function uses a comparison method that does not recur
;; through opaque structures.
;; (check-expect/recur (calc-rbvel 'a 'b) (make-velocity -1 0))
;; (check-expect/recur (calc-rbvel 'b 'a) (make-velocity 1 0))
(check-expect (collision-in-conds? (list col1 col2 col3)) true)
(check-expect (collision-in-conds? (list col2 col3)) false)

(test)

(clear-vars)

;; run an example
(run-animation CUSTOM)
