;; Dualized Haskell Mode
(define-derived-mode dual-lang-mode fundamental-mode
  (setq font-lock-defaults
  	'((("codata\\|cocase\s"
	    . font-lock-function-name-face)
	   ("data\\|case\s"
	    . font-lock-keyword-face))))
  (setq-local comment-start "--")
  (setq-local comment-end   "\n")
  (setq mode-name "dual"))

(autoload 'dual-lang-mode "dual" nil t)
(add-to-list 'auto-mode-alist '("\\.dhs$" . dual-lang-mode))
