(defgroup dl-faces nil
  "Fonts and colours for DL mode.

 These colours are set up to highlight the duality of data and
  codata types.")

(defface dl-codata-face
  '((t (:foreground "#CC0000")))
  "Face highlighting codata keyword"
  :group 'dl-faces)

(defface dl-cocase-face
  '((t (:foreground "#CC5555")))
  "Face highlighting cocase keyword"
  :group 'dl-faces)

(defface dl-data-face
  '((t (:foreground "#0000CC")))
  "Face highlighting data keyword"
  :group 'dl-faces)

(defface dl-case-face
  '((t (:foreground "#5555CC")))
  "Face highlighting case keyword"
  :group 'dl-faces)

(defface dl-keyword-face
  '((t (:foreground "#6920BE")))
  "Face highlighting neutral-ish keywords"
  :group 'dl-faces)

(defface dl-index-face
  '((t (:foreground "#4900AE")))
  "Face highlighting index keyword"
  :group 'dl-faces)

(defface dl-symbols-face
  '((t (:foreground "#19006E")))
  "Face highlighting symbols"
  :group 'dl-faces)

(defface dl-comment-face
  '((t (:foreground "#555555")))
  "Face highlighting symbols"
  :group 'dl-faces)

(defun dl-mode-font-lock-defaults ()
  "Language keywords for DL modes"
  (list
   ;; Codata stuff
   `(,(regexp-opt '("codata") 'words) (0 'dl-codata-face))
   `(,(regexp-opt '("cocase") 'words) (0 'dl-cocase-face))

   ;; Data stuff
   `(,(regexp-opt '("data") 'words) (0 'dl-data-face))
   `(,(regexp-opt '("case") 'words) (0 'dl-case-face))

   ;; Neutralish stuff
   `(,(regexp-opt '("fix" "in" "let") 'words) (0 'dl-keyword-face))
   `(,(regexp-opt '("index") 'words) (0 'dl-index-face))
   `(,(regexp-opt '("=>" "->" ":" "|" "," "#"
                    "(" ")" "{" "}" "[" "]"))
     (0 'dl-symbols-face))))

(defun dl-mode-syntax-table ()
  "Syntax table for DL"
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  ". 123" st)
    (modify-syntax-entry ?\n ">" st)
    st))

(defun dl-mode ()
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table  (dl-mode-syntax-table))
  (set (make-local-variable 'font-lock-defaults)
       (list (dl-mode-font-lock-defaults)))
  (set (make-local-variable 'comment-start) "--")
  (setq major-mode 'dl-mode)
  (setq mode-name "DL")
  "Major mode for editing dual language files")

(autoload 'dl-mode "DL" nil t)
(add-to-list 'auto-mode-alist '("\\.dl$" . dl-mode))

(provide 'dl-mode)
