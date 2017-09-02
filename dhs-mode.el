;; Dualized Haskell Mode

(defvar dual-lang-mode-syntax-table nil "syntax table for dual-lang-mode.")
(setq dual-lang-mode-syntax-table
      (let ((st (make-syntax-table)))
	(modify-syntax-entry ?\- ". 12b" st)
	(modify-syntax-entry ?\n "> b" st)
	st))

;; Definition
(define-derived-mode dual-lang-mode fundamental-mode
  ;; use warning-face for postive syntax and variable-name-face for positive
  ;;   variables
  ;; use type-face for negative syntax and constant-face for negative variables
  (setq font-lock-defaults
  	'((("codata\\|cocase\s"
	    . font-lock-warning-face)
	   ("data\\|case\s"
	    . font-lock-constant-face)
	   )))
  (set-syntax-table dual-lang-mode-syntax-table)
  (setq mode-name "dual"))

;; Loading
(autoload 'dual-lang-mode "dual" nil t)
(add-to-list 'auto-mode-alist '("\\.dhs$" . dual-lang-mode))
