(lang dune 3.23)
(name wait_lang)
(using rocq 0.13)
(generate_opam_files true)

(package
  (name wait_lang)
  (depends
    (rocq-stdlib (>= 9.0)))
  )
