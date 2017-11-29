;
; Append this file in the end of your code to run the tests
;

; Test #0: Method call when instantiating Object
(test/exn
  (interpS
    '(let ([obj (new Object 0)])
       (send obj blah 42))) ; <-- Method does not exist!
  "Class does not respond to the method blah")

; Test #1: User-defiend class inheriting from Object, with methods that change
;          the attribute of the object (shared between them).
(test
  (interpS
    '(let ([Wallet
             (class Object money
                    (method credit amount (:= money (+ money amount)))
                    (method debit amount (:= money (- money amount))) )])
       (let ([wallet (new Wallet 0)])
         (seq (send wallet credit 10)
              (send wallet debit 3)))))
  (numV 7))

; Test #2: User-defined class inheriting from Object, with method that delegates
;          to another via self.
(test
  (interpS
    '(let ([Wallet
             (class Object money
                    (method credit amount (:= money (+ money amount)))
                    (method debit amount (send self credit (~ amount))) )])
       (let ([wallet (new Wallet 0)])
         (seq (send wallet credit 10)
              (send wallet debit 3)))))
  (numV 7))

; Test #3: User-defined class inheriting from Object, calling a method that does
;          not exist.
(test/exn
  (interpS
    '(let ([Wallet
             (class Object money
                    (method credit amount (:= money (+ money amount)))
                    (method debit amount (send self credit (~ amount))) )])
       (let ([wallet (new Wallet 0)])
         (seq (send wallet credit 10)
              (send wallet deduction 3))))) ; <-- Method does not exist!
  "Class does not respond to the method deduction")

; Test #4: User-define class inheriting from another user-defined class,
;          with method from child overriding the parent's implementation,
;          method from parent delegating to overriden method, and method
;          from child accessing attribute of the parent.
(test
  (interpS '(let ([Wallet
                    (class Object money
                           (method credit amount (:= money (+ money amount)))
                           (method debit amount (send self credit (~ amount))) )])
              (let ([WalletWithTaxes
                      (class Wallet tax
                             (method credit amount (:= money (- (+ money amount) tax)))
                             (method total dummy money) )])
                (let ([wallet (new WalletWithTaxes 1)])
                  (seq (send wallet credit 10)
                       (seq (send wallet debit 3)
                            (send wallet total 0))
                       )))))
  (numV 5))

; Test #5: User-define class inheriting from another user-defined class,
;          calling a method that does not exist.
(test/exn
  (interpS '(let ([Wallet
                    (class Object money
                           (method credit amount (:= money (+ money amount)))
                           (method debit amount (send self credit (~ amount))) )])
              (let ([WalletWithTaxes
                      (class Wallet tax
                             (method credit amount (:= money (- (+ money amount) tax)))
                             (method total dummy money) )])
                (let ([wallet (new WalletWithTaxes 1)])
                  (seq (send wallet credit 10)
                       (seq (send wallet debit 3)
                            (send wallet amount 0)) ; <-- Method does not exist!
                       )))))
  "Class does not respond to the method amount")
