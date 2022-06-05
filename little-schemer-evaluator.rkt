#lang scheme
;functions ported over from earlier chapters, incl. functions related to pairs
(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x)))))
(define (a-pair? l)
  (cond
    ((atom? l) #f)
    ((null? l) #f)
    ((null? (cdr l)) #f)
    (else (null? (cdr (cdr l))))))
(define (build first second)
  (cons first
        (cons second '())))
(define (first pair)
  (car pair))
(define (second pair)
  (car (cdr pair)))
(define (third l)
  (car (cdr (cdr l))))

;Functions for dealing with tables (which will later be used to deal with assignments in the evaluator).
;"entry" = pair whose first entry is a set. Can be though of as associating elements of the set with elements of the other list in the pair, based on their position within the list.
;e.g., ((a b c) (1 2 3)) and ((a b c) (1 1 1)) are both examples of entries.
(define new-entry build) ;creates an entry from a set of names and list of values.

(define (lookup-in-entry name entry entry-f) ;returns the value associated with the atom "name" in "entry"; calls user-specified function entry-f on name if name is not found in entry.
  (lookup-in-entry-help name
                        (first entry)
                        (second entry)
                        entry-f))
(define (lookup-in-entry-help name names values entry-f) ;helper function that does the actual work for lookup-in-entry, allowing lookup-in-entry to be called with only a name, entry, and entry-f
  (cond
    ((null? names) (entry-f name))
    ((eq? (car names) name) (car values))
    (else (lookup-in-entry-help name
                                (cdr names)
                                (cdr values)
                                entry-f))))

;table = (possibly empty) list of entries.
(define (extend-table entry table)
  (cons entry table))
(define (lookup-in-table name table table-f) ;analogous to lookup-in-entry; returns the value associated with name in the first entry that contains name.
  (cond
    ((null? table) (table-f name))
    (else (lookup-in-entry name (car table) (lambda (name)
                                              (lookup-in-table name (cdr table) table-f)))))) ;if the first entry does not contain the name we're looking for, we need to recur on the rest of the
                                                                                              ;entries. Hence when we call lookup-in-entry, we pass as entry-f a function that does just that.


;Now onto the evaluator. Each expression is considered to have a type (examples below), and each type is associated with an action. The value function should look at each expression, check its type,
;then apply the relevant action.
;"meaning" is the main function for evaluation: it takes an expression e and a table of assignments, gets the type of e, and applies the relevant action to e and the table. "value" is a "blank-
;slate" version of "meaning" used to evaluate expressions that are supposed to stand alone, not presupposing any assignments. 
(define (value e)
  (meaning e '()))
(define (meaning e table)
  ((expression-to-action e) e table))
;Examples of types/actions are *const, *quote, *identifier, *lambda, *cond, *application.
;this function takes in each expression and returns its type/action:
(define (expression-to-action e)
  (cond
    ((atom? e) (atom-to-action e))
    (else (list-to-action e))))
;an atom will either have type *const, if it is a primitive or number, or *identifier otherwise.
(define (atom-to-action a)
  (cond
    ((number? a) *const)
    ((eq? a #t) *const)
    ((eq? a #f) *const)
    ((eq? a 'cons) *const)
    ((eq? a 'car) *const)
    ((eq? a 'cdr) *const)
    ((eq? a 'null?) *const)
    ((eq? a 'eq?) *const)
    ((eq? a 'atom?) *const)
    ((eq? a 'zero?) *const)
    ((eq? a 'add1) *const)
    ((eq? a 'sub1) *const)
    ((eq? a '+) *const)
    ((eq? a '-) *const)
    ((eq? a '*) *const)
    ((eq? a '/) *const)
    ((eq? a 'expt) *const)
    ((eq? a '=) *const)
    ((eq? a 'remainder) *const)
    ((eq? a 'number?) *const)
    (else *identifier)))
;if a list's first element is an atom, the expression it represents must be either quote applied to something (*quote), a function (*lambda), a conditional (*cond), or an application,
;depending on what exactly that atom is. If a list e's first element is another list, (car e) must be a function being applied to something, so e  gets type *application.
(define (list-to-action e)
  (cond
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote) *quote)
       ((eq? (car e) 'lambda) *lambda)
       ((eq? (car e) 'cond) *cond)
       (else *application)))
    (else *application)))

;among constants, numbers evaluate to themselves, truth values evaluate to #t and #f, while all other constants are primitive functions, which should be "tagged" accordingly so that "apply" can
;deal with them.
(define (*const e table)
  (cond
    ((number? e) e)
    ((eq? e #t) #t)
    ((eq? e #f) #f)
    (else (build 'primitive e))))
;an expression of type *quote is a pair consisting of quote and the thing being quoted. So such an expression should evaluate to the thing being quoted (which is the second element of the pair).
(define (*quote e table)
  (second e))
;The action for *identifier is the first action written so far which uses the table: this is because the table stores the values associated with identifiers, and while that isn't needed to evaluate
;constants and quote expressions, it certainly is needed for identifiers.
(define (*identifier e table)
  (lookup-in-table e table initial-table))
;if an identifier has no value associated with it, then the evaluator should go into some kind of error. This initial-table function is a crude way of doing so: it crashes the program by just
;trying to take the car of the empty list (which doesn't work, since car is defined only for nonempty lists.)
(define (initial-table name)
  (display "Error: no value associated with the identifier ")
  (display name)
  (display ". Will call (car '())) to crash the program")
  (car '()))
;to evaluate a lambda expression, tag it as "non-primitive", then store a copy the table of identifiers and their values alongside the formal parameters and body of the function. (The idea is that
;a function can be completely described by its parameters and body, but that knowing the environment/identifier table will be necessary when applying the function.) Note that since a function
;is here represented as (lambda (formals) (body)), its formals + body is just the cdr of the function.
(define (*lambda e table)
  (build 'non-primitive
         (cons table (cdr e))))
;helper functions for dealing with evaluated lambda-expressions
(define table-of first)
(define formals-of second)
(define body-of third)
;evaluating cond expressions. These are represented as (cond ((question) (answer)) ((question) (answer))...) I.e. a list whose car is 'cond, and whose cdr is a list of pairs, each consisting of a
;question and an "answer" (the thing to be executed if the question evaluates to true). An "else..." clause is considered to be a question which always evaluates to true. There is no provision in
;case none of the cond's questions evaluate to true (i.e. lines-of becomes empty before finding an expression that evaluates to true). Lines (question-answer pairs) are evaluated in sequence, and
;evaluation terminates once a true question is found.
(define cond-lines-of cdr)
(define question-of first)
(define answer-of second)

(define (*cond e table)
  (evcon (cond-lines-of e) table))

(define (else? x)
  (cond
    ((atom? x) (eq? x 'else))
    (else #f)))
(define (evcon lines table)
  (cond
    ((else? (question-of (car lines))) (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table) (meaning (answer-of (car lines)) table))
    (else (evcon (cdr lines) table))))

;application: list whose car is a function, cdr is its arguments. To evaluate it, need to find the meaning of all its arguments, find the meaning of its function, and apply the function to the
;arguments.
(define function-of car)
(define arguments-of cdr)

(define (evlis list table) ;turns a list of representations of expressions into a list of the meanings of all the elements of the initial list.
  (cond
    ((null? list) '())
    (else (cons (meaning (car list) table)
                (evlis (cdr list) table)))))

(define (*application e table)
  (apply (meaning (function-of e) table)
         (evlis (arguments-of e) table)))
;a function is represented as ('primitive name) or ('non-primitive (table formals body)). (The list (table formals body) is called the "closure" of a function.) The "apply" function should
;determine which kind of function the function is, then call an "apply-primitive" or "apply-closure" function which will do the actual work. If a function is not in one of these representations,
;apply gives no answer.
(define (primitive? function)
  (eq? (first function) 'primitive))
(define (non-primitive? function)
  (eq? (first function) 'non-primitive))
;function is an expression of one of the forms given above; vals is a list of the things to which the function is being applied. By the time a function reaches this point, *application has already
;processed vals into a list of the meanings of its components.
(define (apply function vals)
  (cond
    ((primitive? function) (apply-primitive (second function) vals)) ;here (second function) is the name of the primitive 
    ((non-primitive? function) (apply-closure (second function) vals)))) ;here (second function) is the closure, (table formals body)

;apply-primitive is one big cond expression. As implemented here, it makes no attempt to check for errors and assumes that it has been passed a properly-called primitive function.
(define (apply-primitive name vals)
  (cond
    ((eq? name 'cons) (cons (first vals) (second vals)))
    ((eq? name 'car) (car (first vals))) ;note that (first vals) is itself a list: in this case, the list whose car we want
    ((eq? name 'cdr) (cdr (first vals)))
    ((eq? name 'null?) (null? (first vals)))
    ((eq? name 'eq?) (eq? (first vals) (second vals)))
    ((eq? name 'atom?) (atom? (first vals)))
    ((eq? name 'zero?) (zero? (first vals)))
    ((eq? name 'add1) (add1 (first vals)))
    ((eq? name 'sub1) (sub1 (first vals)))
    ((eq? name '+) (+ (first vals) (second vals))) ;note that all of the arithmetic operations have been defined as accepting only 2 arguments. So e.g. (+ 1 2 3) must be rewritten as 
    ((eq? name '-) (- (first vals) (second vals))) ;(+ 1 (+ 2 3)) in order to be accepted by the evaluator.
    ((eq? name '*) (* (first vals) (second vals)))
    ((eq? name '/) (/ (first vals) (second vals)))
    ((eq? name '=) (= (first vals) (second vals)))
    ((eq? name 'remainder) (remainder (first vals) (second vals)))
    ((eq? name 'expt) (expt (first vals) (second vals)))
    ((eq? name 'number?) (number? (first vals)))))
;apply-closure needs to extend the table/environment. More specifically, it needs to evaluate the body of the function while knowing that each occurence of one of the function's formals in the body
;should evaluate to whatever value was passed in for that formal. This is done by adding a new entry to the table of the form (formals values), which allows for each formal to be mapped to the
;value that was passed to it, and then calling meaning on the body of the function and the extended table.
(define (apply-closure closure vals)
  (meaning (body-of closure)
           (extend-table (new-entry (formals-of closure) vals)
                         (table-of closure))))

(value '(lambda (x) (* x x)))
(value '((lambda (x) (* x x)) 3))
(value 
'(((lambda (almost-recursive)
    ((lambda (f) (f f))
     (lambda (f) (almost-recursive (lambda (x y) ((f f) x y))))))
  (lambda (gcd)
    (lambda (a b)
      (cond
        ((= b 0) a)
        (else (gcd b (remainder a b)))))))
 35 25))
(value
'((lambda (almost-recursive)
    ((lambda (f) (f f))
     (lambda (f) (almost-recursive (lambda (x y) ((f f) x y))))))
  (lambda (gcd)
    (lambda (a b)
      (cond
        ((= b 0) a)
        (else (gcd b (remainder a b))))))))
(value '(+ 1 (+ 2 3)))
(value '#t)
(value '(cond
          (#t 1)
          (else 2)))
