#lang racket

(require web-server/servlet
         web-server/http
         json
         web-server/servlet-env)


(define (start req)
  (define u (request-uri req))
  (define meth (path/param-path (first (url-path u))))
  (cond
    [(string=? meth "main")
     (response/xexpr
       `(html (head (title "Hello world!"))
              (body (p "Hey out there!"))))]
    [(string=? meth "eval")
     (define to-eval (bindings-assq
                       #"code"
                         (request-bindings/raw req)))
     (define stdin (open-input-bytes (binding:form-value to-eval)))
     (define stdin-copy (open-input-bytes (binding:form-value to-eval)))
     (define stdout (open-output-string "stdout"))
     (define stderr (open-output-string "stderr"))
     (define stdout-dsg (open-output-string "stdout-dsg"))
     (define stderr-dsg (open-output-string "stderr-dsg"))
     (define out
      (parameterize ([current-directory "/home/s5/src/LambdaS5/tests"])
        (define plist
          (process*/ports stdout stdin stderr "/home/s5/src/LambdaS5/tests/s5i"))
        (define plist2
          (process*/ports stdout-dsg stdin-copy stderr-dsg "/home/s5/src/LambdaS5/tests/s5-print"))
        ((fifth plist) 'wait)
        ((fifth plist2) 'wait)
        (define out-str (get-output-string stdout))
        (define err-str (get-output-string stderr))
        (define desugared-string (get-output-string stdout-dsg))
        (define desugared-err (get-output-string stderr-dsg))
        (jsexpr->string (make-immutable-hash (list
                                              (cons 'stdout-eval out-str)
                                              (cons 'stderr-eval err-str)
                                              (cons 'stdout-dsg desugared-string)
                                              (cons 'stderr-dsg desugared-err))))))
     (response/xexpr out)]))

(serve/servlet start
               #:port 8080
               #:servlet-regexp #rx""
               #:listen-ip #f
               #:command-line? #t)
