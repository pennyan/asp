;; package.lsp -- I adapted this from an earlier project.  Undoubtably,
;;    the list of imports could be trimmed.
(in-package "ACL2")

;; load other packages needed to define our new packages...
(include-book "std/lists/top" :dir :system)
(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)

;; define our new packages
(defpkg "ASP"
  (set-difference-eq
   (union-eq
    *acl2-exports*
    *standard-acl2-imports*
    *common-lisp-symbols-from-main-lisp-package*
    ;; Things we want to export
    nil  ;; I'll figure this out later
    ;; Things we want to import
    '(b*
      define
      maybe-natp
      l<
      defsort
      make-fal
      defconsts
      raise
      tshell-ensure
      tshell-call
      defrule
      defrulel
      defruledl
      defruled
      fchecksum-obj
      trans-eval
      parse-clause-id
      set-raw-mode-on
      disjoin
      more-returns
      natp-listp
      with-fast-alists
      maybe-stringp
      prefixp
      plev
      plev-max
      two-nats-measure
      bitp
      defxdoc
      defsection
      str-fix
      bool-fix
      symbol-fix
      list-fix
      assert!
      boolean-listp
      boolean-list-fix
      lnfix

      ;; str::cat
      str::natstr
      str::strtok
      str::count
      str::substrp
      str::isubstrp
      str::strpos
      str::firstn-chars
      str::strval
      str::search
      str::strnat<
      str::string-list-fix
      str::join
      str::make-character-list
      str::character-list-fix

      fty::defalist
      fty::defprod
      fty::deflist
      fty::deftagsum
      fty::deffixtype
      fty::deftypes
      fty::defoption
      fty::lposfix

;;      set::union
      set::difference
      )
    )
   ;; Things to remove
   '()))
