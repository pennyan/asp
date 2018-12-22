(in-package "ASP")
(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.

(define int-to-char-list ((i natp) (u character-listp))
  :returns (u2 character-listp)
  (b* ((u (character-list-fix u))
       ((if (zp i)) u)
       (rst (nonnegative-integer-quotient i 10))
       (lsd (- i (* 10 rst))))
    (int-to-char-list
     rst
     (cons (code-char (+ (char-code #\0) lsd)) u))))

(encapsulate nil
  (local (defthm stupid-lemma
           (implies (character-listp x) (character-listp (acl2::rev x)))))

  (define frac-to-rev-char-list ((r rationalp) (u character-listp) (prec natp))
    :guard (<= 0 r)
    :measure (nfix prec)
    :returns (u2 character-listp)
    (b* ((u (character-list-fix u))
         ((if (equal 0 r)) u)
         (p 524287)
         ((if (zp prec))
          (append
           (acl2::rev
            (append (list #\? #\#)
                    (int-to-char-list (abs (rem (numerator r) p)) nil)
                    (list #\/ )
                    (int-to-char-list (abs (rem (denominator r) p)) nil)
                    (list #\? )))
           u))
         (r10 (* 10 r))
         (d (nonnegative-integer-quotient (numerator r10) (denominator r10)))
         (rst (- r10 d))
         ((unless (and (<= 0 d) (< d 10) (<= 0 rst))) u))
      (frac-to-rev-char-list
       rst
       (cons (code-char (+ (char-code #\0) d)) u)
       (1- prec))))

  (define rational-to-string ((r rationalp) (prec natp))
    :returns (s stringp)
    :guard-debug t
    (b* ((abs-r (abs r))
         (int-part (nonnegative-integer-quotient (numerator abs-r)
                                                 (denominator abs-r)))
         (si (int-to-char-list int-part nil))
         (si (cond ((< r 0) (cons #\- si))
                   ((> r 0) si)
                   (t '(#\0))))
         (frac-part (- abs-r int-part))
         (sf (if (<= frac-part 0)
                 nil
               (cons #\. (acl2::rev
                          (frac-to-rev-char-list frac-part nil prec))))))
      (coerce (concatenate 'list si sf) 'string))))
