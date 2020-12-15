# LangSMC - Language-based Secure Multiparty Computation

Secure multiparty computation (SMC) allows for complex computations over encrypted data. Privacy concerns for cloud applications makes this a highly desired technology and recent performance improvements show that it is practical. To make SMC accessible to non-experts and empower its use in varied applications, many domain-specific compilers are being proposed.

In this work we review the role of these compilers and provide a formal treatment of the core steps that they perform to bridge the abstraction gap between high-level ideal specifications and efficient SMC protocols. Our abstract framework bridges this secure compilation problem across two dimensions: 

1. Language-based source- to target-level semantic and efficiency gaps
2. Cryptographic ideal- to real-world security gaps

We link the former to the setting of certified compilation, paving the way to leverage long-run efforts such as CompCert in future high-assurance SMC compilers. Security is framed in the standard cryptographic sense. This repository reports on the machine-checked formalisation of our results carried out in EasyCrypt, an interactive theorem prover for code-based cryptographic security proofs.

## Repository organisation

We disclose an image of the main EasyCrypt repository under the `easycrypt` submodule folder. 
All EasyCrypt scripts that encompass our formalisation can be found in the `proof/src` folder.

## Building the proof

### Requirements

Because the only third-party tool that is used in this project is EasyCrypt, our requirements are essentially the requirements of EasyCrypt.
We refer the user to the README file in the EasyCrypt repository - https://www.easycrypt.info/trac/browser/README.md?rev=1.0 - for clear instructions on how to install such dependencies.

### Building EasyCrypt

Once all EasyCrypt installation requirements are installed, EasyCrypt can be locally built via

`make easycrypt`

### Verifying the proof

Finally, the formalisation can be verified by typing 

`make check-proof`

which launches an EasyCrypt test script and applies it to all files that comprise the proof.

## Proof documentation

A comprehensive description of our EasyCrypt formalisation can be found in http://langsmc.readthedocs.io.
However, the documentation can be locally build using the command

`make docs-[target]`

where `target` can be either *html* or *latex*. This command will
create the appropriate documentation files under the `docs/build`
folder.
