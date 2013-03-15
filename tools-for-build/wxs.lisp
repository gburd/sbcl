;;;; Generate WiX XML Source, from which we eventually generate the .MSI

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

;;;; XML generation

(defvar *indent-level* 0)

(defvar *sbcl-source-root*
  (truename
   (merge-pathnames (make-pathname :directory (list :relative :up))
                    (make-pathname :name nil :type nil :defaults *load-truename*))))

(defun print-xml (sexp &optional (stream *standard-output*))
  (destructuring-bind (tag &optional attributes &body children) sexp
    (when attributes (assert (evenp (length attributes))))
    (format stream "~VT<~A~{ ~A='~A'~}~@[/~]>~%"
            *indent-level* tag attributes (not children))
      (let ((*indent-level* (+ *indent-level* 3)))
        (dolist (child children)
          (unless (listp child)
            (error "Malformed child: ~S in ~S" child children))
          (print-xml child stream)))
      (when children
        (format stream "~VT</~A>~%" *indent-level* tag))))

(defun xml-1.0 (pathname sexp)
  (with-open-file (xml pathname :direction :output :if-exists :supersede
                       :external-format :ascii)
     (format xml "<?xml version='1.0'?>")
     (print-xml sexp xml)))

(defun application-name ()
  (format nil "Steel Bank Common Lisp ~A (~A)" (lisp-implementation-version) (machine-type)))

(defun version-digits (&optional (horrible-thing (lisp-implementation-version)))
  "Turns something like 0.pre7.14.flaky4.13 (see version.lisp-expr)
  into an acceptable form for WIX (up to four dot-separated numbers)."
  (with-output-to-string (output)
    (loop repeat 4
          with position = 0
          for separator = "" then "."
          for next-digit = (position-if #'digit-char-p horrible-thing
                                    :start position)
          while next-digit
          do (multiple-value-bind (number end)
                 (parse-integer horrible-thing :start next-digit :junk-allowed t)
               (format output "~A~D" separator number)
               (setf position end)))))

;;;; GUID generation
;;;;
;;;; Apparently this willy-nilly regeneration of GUIDs is a bad thing, and
;;;; we should probably have a single GUID per release / Component, so
;;;; that no matter by whom the .MSI is built the GUIDs are the same.
;;;;
;;;; Something to twiddle on a rainy day, I think.

(load-shared-object "OLE32.DLL")

(define-alien-type uuid
    (struct uuid
            (data1 unsigned-int)
            (data2 unsigned-short)
            (data3 unsigned-short)
            (data4 (array unsigned-char 8))))

(define-alien-routine ("CoCreateGuid" co-create-guid) int (guid (* uuid)))

(defun uuid-string (uuid)
  (declare (type (alien (* uuid)) uuid))
  (let ((data4 (slot uuid 'data4)))
    (format nil "~8,'0X-~4,'0X-~4,'0X-~2,'0X~2,'0X-~{~2,'0X~}"
            (slot uuid 'data1)
            (slot uuid 'data2)
            (slot uuid 'data3)
            (deref data4 0)
            (deref data4 1)
            (loop for i from 2 upto 7 collect (deref data4 i)))))

(defun make-guid ()
  (let (guid)
    (unwind-protect
         (progn
           (setf guid (make-alien (struct uuid)))
           (co-create-guid guid)
           (uuid-string guid))
      (free-alien guid))))

(defun list-all-contribs ()
  (loop for flag in (directory "../contrib/*/test-passed")
        collect (car (last (pathname-directory flag)))))

(defvar *id-char-substitutions* '((#\\ . #\_)
                                  (#\/ . #\_)
                                  (#\: . #\.)
                                  (#\- . #\.)))

(defun id (string)
  ;; Mangle a string till it can be used as an Id. A-Z, a-z, 0-9, and
  ;; _ are ok, nothing else is.
  (map 'string (lambda (c)
                 (or (cdr (assoc c *id-char-substitutions*))
                     c))
       string))

(defun directory-id (name)
  (id (format nil "Directory_~A" (enough-namestring name *sbcl-source-root*))))

(defun file-id (pathname)
  (id (format nil "File_~A" (enough-namestring pathname *sbcl-source-root*))))

(defparameter *ignored-directories* '("CVS" ".svn" "test-output"))

(defparameter *pathname-type-abbrevs*
  '(("lisp" . "lsp")
    ("fasl" . "fas")
    ("SBCL" . "txt") ; README.SBCL -> README.txt
    ("texinfo" . "tfo")
    ("lisp-temp" . "lmp")
    ("html" . "htm")))

(defparameter *components* nil)

(defun component-id (pathname)
  (let ((id (id (format nil "Contrib_~A" (enough-namestring pathname *sbcl-source-root*)))))
    (push id *components*)
    id))

(defun ref-all-components ()
  (prog1
      (mapcar (lambda (id)
                `("ComponentRef" ("Id" ,id)))
              *components*)
    (setf *components* nil)))

(defun collect-1-component (root)
  `("Directory" ("Name" ,(car (last (pathname-directory root)))
                 "Id" ,(directory-id root))
    ("Component" ("Id" ,(component-id root)
                  "Guid" ,(make-guid)
                  "DiskId" 1)
     ,@(loop for file in (directory
                          (make-pathname :name :wild :type :wild :defaults root))
             when (or (pathname-name file) (pathname-type file))
             collect `("File" ("Name" ,(file-namestring file)
                               "Id" ,(file-id file)
                               "Source" ,(enough-namestring file)))))))

(defun directory-empty-p (dir)
  (null (directory (make-pathname :name :wild :type :wild :defaults dir))))

(defun collect-components (root)
  (append (unless (directory-empty-p root) (list (collect-1-component root)))
          (loop for directory in
                (directory
                 (merge-pathnames (make-pathname
                                   :directory '(:relative :wild)
                                   :name nil :type nil)
                                  root))
                unless (member (car (last (pathname-directory directory)))
                               *ignored-directories* :test #'equal)
                append (collect-components directory))))

(defun collect-contrib-components ()
  (loop for contrib in (directory "../contrib/*/test-passed")
        append (collect-components (make-pathname :name nil
                                                  :type nil
                                                  :version nil
                                                  :defaults contrib))))

(defun make-extension (type mime)
  `("Extension" ("Id" ,type "ContentType" ,mime)
    ("Verb" ("Id" ,(format nil "load_~A" type)
             "Argument" "--core \"[#sbcl.core]\" --load \"%1\""
             "Command" "Load with SBCL"
             "Target" "[#sbcl.exe]"))))

(defun write-wxs (pathname)
  ;; both :INVERT and :PRESERVE could be used here, but this seemed
  ;; better at the time
  (xml-1.0
   pathname
   `("Wix" ("xmlns" "http://schemas.microsoft.com/wix/2006/wi")
     ("Product" ("Id" "*"
                 "Name" ,(application-name)
                 "Version" ,(version-digits)
                 "Manufacturer" "http://www.sbcl.org"
                 "UpgradeCode" "BFF1D4CA-0153-4AAC-BB21-06DC4B8EAD7D"
                 "Language" 1033)
      ("Package" ("Id" "*"
                  "Manufacturer" "http://www.sbcl.org"
                  "InstallerVersion" 200
                  "Compressed" "yes"
                  #+x86-64 "Platform" #+x86-64 "x64"
                  "InstallScope" "perMachine"))
      ("Media" ("Id" 1
                "Cabinet" "sbcl.cab"
                "EmbedCab" "yes"))
      ("Property" ("Id" "PREVIOUSVERSIONSINSTALLED"
                   "Secure" "yes"))
      ("Upgrade" ("Id" "BFF1D4CA-0153-4AAC-BB21-06DC4B8EAD7D")
       ("UpgradeVersion" ("Minimum" "1.0.0"
                          "Maximum" "99.0.0"
                          "Property" "PREVIOUSVERSIONSINSTALLED"
                          "IncludeMinimum" "yes"
                          "IncludeMaximum" "no")))
      ("InstallExecuteSequence" ()
       ("RemoveExistingProducts" ("After" "InstallInitialize")))
      ("Directory" ("Id" "TARGETDIR"
                    "Name" "SourceDir")
       ("Directory" ("Id" "ProgramMenuFolder")
        ("Component" ("Id" "SBCL_Shortcut"
                      "Guid" ,(make-guid))
         ("Shortcut" ("Id" "sbcl.lnk"
                      "Name" ,(application-name)
                      "Target" "[INSTALLDIR]sbcl.exe"
                      "Arguments" "--core \"[#sbcl.core]\""))
         ("RegistryValue" ("Root" "HKCU"
                           "Key" ,(application-name)
                           "Name" "installed"
                           "Type" "integer"
                           "Value" "1"
                           "KeyPath" "yes"))))
       ("Directory" ("Id" #-x86-64 "ProgramFilesFolder" #+x86-64 "ProgramFiles64Folder"
                     "Name" "PFiles")
        ("Directory" ("Id" "BaseFolder"
                      "Name" "Steel Bank Common Lisp")
         ("Directory" ("Id" "VersionFolder"
                       "Name" ,(lisp-implementation-version))
          ("Directory" ("Id" "INSTALLDIR")
           ("Component" ("Id" "SBCL_SetHOME"
                         "Guid" ,(make-guid)
                         "DiskId" 1)
            ("Environment" ("Id" "Env_SBCL_HOME"
                            "System" "yes"
                            "Action" "set"
                            "Name" "SBCL_HOME"
                            "Part" "all"
                            "Value" "[INSTALLDIR]")))

           ("Component" ("Id" "SBCL_SetPATH"
                         "Guid" ,(make-guid)
                         "DiskId" 1)
            ("Environment" ("Id" "Env_PATH"
                            "System" "yes"
                            "Action" "set"
                            "Name" "PATH"
                            "Part" "last"
                            "Value" "[INSTALLDIR]")))
           ("Component" ("Id" "SBCL_Base"
                         "Guid" ,(make-guid)
                         "DiskId" 1)
            ;; If we want to associate files with SBCL, this
            ;; is how it's done -- but doing this by default
            ;; and without asking the user for permission Is
            ;; Bad. Before this is enabled we need to figure out
            ;; how to make WiX ask for permission for this...
            ;; ,(make-extension "fasl" "application/x-lisp-fasl")
            ;; ,(make-extension "lisp" "text/x-lisp-source")
            ("File" ("Name" "sbcl.exe"
                     "Source" "../src/runtime/sbcl.exe"))
            ("File" ("Name" "sbcl.core"
                     "Source" "sbcl.core")))
           ,@(collect-contrib-components))))))
      ("Feature" ("Id" "Minimal"
                  "Title" "SBCL Executable"
                  "ConfigurableDirectory" "INSTALLDIR"
                  "Level" 1)
       ("ComponentRef" ("Id" "SBCL_Base"))
       ("Feature" ("Id" "Contrib" "Level" 1 "Title" "Contributed Modules")
                  ,@(ref-all-components))
       ("Feature" ("Id" "Shortcut" "Level" 1 "Title" "Add Start Menu Shortcut")
                  ("ComponentRef" ("Id" "SBCL_Shortcut")))
       ("Feature" ("Id" "SetPath" "Level" 1 "Title" "Set Environment Variable: PATH")
                  ("ComponentRef" ("Id" "SBCL_SetPATH")))
       ;; SetHome is still enabled by default (level 1), because SBCL
       ;; does not yet support running without SBCL_HOME:
       ("Feature" ("Id" "SetHome" "Level" 1 "Title" "Set Environment Variable: SBCL_HOME")
                  ("ComponentRef" ("Id" "SBCL_SetHOME"))))
      ("WixVariable" ("Id" "WixUILicenseRtf"
                      "Value" "License.rtf"))
      ("Property" ("Id" "WIXUI_INSTALLDIR" "Value" "INSTALLDIR"))
      ("UIRef" ("Id" "WixUI_FeatureTree"))))))
