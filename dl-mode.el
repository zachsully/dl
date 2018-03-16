(defvar dl-mode-syntax-table nil "syntax table for dl-mode.")
(setq dual-lang-mode-syntax-table
      (let ((st (make-syntax-table)))
	(modify-syntax-entry ?\- ". 12b" st)
	(modify-syntax-entry ?\n "> b" st)
	st))

;; Definition
(define-derived-mode dl-mode fundamental-mode
  ;; use warning-face for postive syntax and variable-name-face for positive
  ;;   variables
  ;; use type-face for negative syntax and constant-face for negative variables
  (setq font-lock-defaults
  	'((("codata\s"              . font-lock-warning-face)
	   ("cocase\s"              . font-lock-variable-name-face)
	   ("data\s"                . font-lock-constant-face)
	   ("case\s"                . font-lock-type-face)
           ("\(fix\|in\|let\)\s"    . font-lock-string-face)
	   )))
  ;; (set-syntax-table dual-lang-mode-syntax-table)
  (setq set-input-method "delimiters")
  (setq mode-name "dl-mode"))

;; Loading
(autoload 'dl-mode "dl-mode" nil t)
(add-to-list 'auto-mode-alist '("\\.dl$" . dl-mode))
