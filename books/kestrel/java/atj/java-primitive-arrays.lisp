; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "types")

(include-book "kestrel/std/system/function-name-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-primitive-arrays
  :parents (atj-implementation)
  :short "ATJ's representation of Java primitive arrays and operations on them."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to have ATJ generate Java code
     that manipulates Java primitive arrays,
     we use an approach similar to "
    (xdoc::seetopic "atj-java-primitives" "the one for Java primitive values")
    ". We use ACL2 functions that correspond to
     the Java primitive arrays and operations on them:
     when ATJ encounters these specific ACL2 functions,
     it translates them to corresponding Java constructs
     that operate on Java primitive arrays;
     this happens only when @(':deep') is @('nil') and @(':guards') is @('t').")
   (xdoc::p
    "The discussion "
    (xdoc::seetopic "atj-java-primitives" "here")
    " about derivations targeting
     the ACL2 functions that represent Java primitive values
     applies to Java primitive arrays as well.")
   (xdoc::p
    "As discussed "
    (xdoc::seetopic "atj-java-primitive-array-model" "here")
    ", currently the ACL2 functions that represent Java primitive arrays
     are part of ATJ, but (perhaps some generalization of them) could be
     part of the "
    (xdoc::seetopic "language" "language formalization")
    " at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-reads*
  :short "List of (the names of) the ACL2 functions that model
          the reading of components from Java primitive arrays."
  '(boolean-array-read
    char-array-read
    byte-array-read
    short-array-read
    int-array-read
    long-array-read
    float-array-read
    double-array-read))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-lengths*
  :short "List of (the names of) the ACL2 functions that model
          the retrieval of lengths of Java primitive arrays."
  '(boolean-array-length
    char-array-length
    byte-array-length
    short-array-length
    int-array-length
    long-array-length
    float-array-length
    double-array-length))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-constrs*
  :short "List of (the names of) the ACL2 functions that model
          the construction of Java primitive arrays."
  '(boolean-array-of-length
    char-array-of-length
    byte-array-of-length
    short-array-of-length
    int-array-of-length
    long-array-of-length
    float-array-of-length
    double-array-of-length))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-constrs-init*
  :short "List of (the names of) the ACL2 functions that model
          the construction of Java primitive arrays with initializers."
  :long
  (xdoc::topstring-p
   "We exclude the functions that model
    the construction of @('float') and @('double') arrays with initializers,
    because we only have abstract models of those values for now.")
  '(boolean-array-with-comps
    char-array-with-comps
    byte-array-with-comps
    short-array-with-comps
    int-array-with-comps
    long-array-with-comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive array operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This just consists of the read, length, and constructor functions for now.
     The write functions will be added in the future."))
  (append *atj-java-primarray-reads*
          *atj-java-primarray-lengths*
          *atj-java-primarray-constrs*
          *atj-java-primarray-constrs-init*)
  ///
  (assert-event (function-name-listp *atj-java-primarray-fns* (w state)))
  (assert-event (no-duplicatesp-eq *atj-java-primarray-fns*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-java-primarray-fn-p ((fn symbolp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 funcion (symbol) is one that models
          Java primitive array operations."
  (and (member-eq fn *atj-java-primarray-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-types-for-java-primitive-arrays
  :short "ATJ types for the Java primitive array operations."

  ;; read operations:

  (def-atj-main-function-type boolean-array-read (:jboolean[] :jint) :jboolean)

  (def-atj-main-function-type char-array-read (:jchar[] :jint) :jchar)

  (def-atj-main-function-type byte-array-read (:jbyte[] :jint) :jbyte)

  (def-atj-main-function-type short-array-read (:jshort[] :jint) :jshort)

  (def-atj-main-function-type int-array-read (:jint[] :jint) :jint)

  (def-atj-main-function-type long-array-read (:jlong[] :jint) :jlong)

  (def-atj-main-function-type float-array-read (:jfloat[] :jint) :jfloat)

  (def-atj-main-function-type double-array-read (:jdouble[] :jint) :jdouble)

  ;; length operations:

  (def-atj-main-function-type boolean-array-length (:jboolean[]) :jint)

  (def-atj-main-function-type char-array-length (:jchar[]) :jint)

  (def-atj-main-function-type byte-array-length (:jbyte[]) :jint)

  (def-atj-main-function-type short-array-length (:jshort[]) :jint)

  (def-atj-main-function-type int-array-length (:jint[]) :jint)

  (def-atj-main-function-type long-array-length (:jlong[]) :jint)

  (def-atj-main-function-type float-array-length (:jfloat[]) :jint)

  (def-atj-main-function-type double-array-length (:jdouble[]) :jint)

  ;; constructors from length:

  (def-atj-main-function-type boolean-array-of-length (:jint) :jboolean[])

  (def-atj-main-function-type char-array-of-length (:jint) :jchar[])

  (def-atj-main-function-type byte-array-of-length (:jint) :jbyte[])

  (def-atj-main-function-type short-array-of-length (:jint) :jshort[])

  (def-atj-main-function-type int-array-of-length (:jint) :jint[])

  (def-atj-main-function-type long-array-of-length (:jint) :jlong[])

  (def-atj-main-function-type float-array-of-length (:jint) :jfloat[])

  (def-atj-main-function-type double-array-of-length (:jint) :jdouble[])

  ;; constructors from components:

  (def-atj-main-function-type boolean-array-with-comps (:avalue) :jboolean[])

  (def-atj-main-function-type char-array-with-comps (:avalue) :jchar[])

  (def-atj-main-function-type byte-array-with-comps (:avalue) :jbyte[])

  (def-atj-main-function-type short-array-with-comps (:avalue) :jshort[])

  (def-atj-main-function-type int-array-with-comps (:avalue) :jint[])

  (def-atj-main-function-type long-array-with-comps (:avalue) :jlong[]))
