# Simple calculator in C

### Build
```sh
cc nob.c -o nob
./nob
```
This should be done only once, after that if you need to rebuild, just run `./nob`.

Note that `./nob` also immediately runs `./calc`, if you didn't change anything, you can just run `./calc`

If you dont want to build with nob, you can build with any C compiler like this:
```sh
cc calc.c -o calc -lreadline -lm
```
Currently calculator depends only on GNU `readline` and `math` libraries.

### Syntax
This calculator supports basic arithmetic operations such as addition, subtraction, unary negation, multiplication, raising to a power and division.
And you can group expressions into parentheses:
```
(2 - 3 / 12 * (-2)) + (13 * 12**-5 / 10)
```

Also you can very easily define variables, by simply assigning a value to then:
```
my_var = 3.14
```
As you can see calculator also supports floating point numbers, you can write them as you wish:
```
3.14 - .1 / 12.
```
To define a function, there is two ways:
* **Normal function:**

    ```
    $my_func(a, b): a + b
    ```
    Here is:
    ```
    $my_func(a, b): a + b
     ^~~~~~~ ^~~~   ^~~~~
     |       |      |- function body
     |       |
     |       |- parameters list
     |
     |- function name
    ```
    To return a value, you dont need to do anything, it will be returned anyway.

* **Anonymous function:**

    ```
    $(foo, bar): foo / bar
    ```
    This function simply doesn't have a name and will not be defined, but you can assign it to a variable or pass into another function
