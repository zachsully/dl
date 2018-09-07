(defgroup dl-faces nil
  "Fonts and colours for DL mode.

 These colours are set up to highlight the duality of data and
  codata types.")

(defface dl-codata-face
  '((t (:inherit font-lock-warning-face)))
  "Face highlighting codata keyword"
  :group 'dl-faces)

;; (defface dl-cocase-face
;;   '((t (:inherit font-lock-variable-name-face)))
;;   "Face highlighting cocase keyword"
;;   :group 'dl-faces)

;; (defface dl-keyword-face
;;   '((t (:inherit font-lock-string-face))))


(defconst dl-mode-font-lock-defaults
  `(;; Codata stuff
    (,(regexp-opt '("codata") 'words) . font-lock-warning-face)
    (,(regexp-opt '("cocase") 'words) . font-lock-variable-name-face)

    ;; Data stuff
    (,(regexp-opt '("data") 'words) . font-lock-constant-face)
    (,(regexp-opt '("case") 'words) . font-lock-type-face)

    ;; Neutralish stuff
    (,(regexp-opt '("fix" "in" "let") 'words) . font-lock-string-face)
    (,(regexp-opt '("index") 'words) . font-lock-keyword-face)
    (,(regexp-opt '("=>" "->" ":" "|" "," "#"
                    "(" ")" "{" "}" "[" "]"))
     . font-lock-preprocessor-face)
    )
  "Language keywords for DL modes")

(defun dl-mode-syntax-table ()
  "Syntax table for DL"
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?- ". 23b" st)
    (modify-syntax-entry ?{ ". 1" st)
    (modify-syntax-entry ?} ". 4" st)
    (modify-syntax-entry ?\n ">" st)
    st))

(defun dl-mode ()
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table  (dl-mode-syntax-table))
  (set (make-local-variable 'font-lock-defaults) `(,dl-mode-font-lock-defaults))
  (setq major-mode 'dl-mode)
  (setq mode-name "DL")
  "Major mode for editing dual language files")

(autoload 'dl-mode "DL" nil t)
(add-to-list 'auto-mode-alist '("\\.dl$" . dl-mode))

(provide 'dl-mode)
