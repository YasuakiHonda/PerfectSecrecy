# Perfect Secrecy

## What's in this project

C. Shannon established a connection between information security and mathematics in his fameous paper "Communication Theory of Secrecy Systems", 1949.
In the paper, 
* Cipher system is mathematically defined,
* The notion of perfect secrecy of a cipher system is defined,
* The general limitation that the key set size must be larger than the message set was stated, and
* One Time Pad cipher was shown to be perfect secrecy.

In this repository, formal proof verifier Lean4 prover and mathlib4 is used to
* formalize the cipher systems,
* formalize the notion of perfect secrecy,
* formalize the key set size limitation as a theorem and proved, and
* One Time Pad cipher is defined and proved to be perfect secrecy.

Under the folder PerfectSecrecy, the following files are provided:
* PerfectSecrecy_Def.lean : definition of a cipher system and the definition of perfect secrecy are given.
* PerfectSecrecy_Key_Size.lean: Key size limitation theorem on perfect secrecy and its proof are given.
* OTP.lean : One Time Pad cipher is defined and proven to be perfect secrecy.

## How to use
You can download the whole folder structure as a zip file by pressing Code button and choose "Download ZIP".
Then you need to expand the zip to a folder.
Please invoke the following commands in the folder:
  lake exe cache get
  lake build

After things are done, you can open the folder using VSCode to start !

## Author and License
As this is a mathematical proof, you can do whatever you want.
The files are covered by MIT license for now, but if needed you can request a different licensing terms for your needs.

Author: Yasuaki Honda, an Independent Developer in Japan
