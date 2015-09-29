# Bellmania

First make sure all the relevant packages are installed:

```
npm install
```

Then you can compile the grammar with nearley:

```
nearleyc src/lambda.ne -o src/lambda.js
```

Compile the LiveScript files:
```
lsc -co src src-ls
```

Open the app with
```
node_modules/.bin/nw
```

and then you can start typing expressions in the code editor and parsing them! Have fun!