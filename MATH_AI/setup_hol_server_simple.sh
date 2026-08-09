#!/bin/bash

# Simple HOL Light Server Setup with clean paths
HOL_PATH="/Users/raobalag/Desktop/hol-light/hol.sh"
SERVER_PATH="/Users/raobalag/Desktop/hol_server"
S2N_BIGNUM_PATH="/Users/raobalag/Desktop/s2n-bignum"
PORT=2012

echo "Starting HOL Light Server (simple setup) on port $PORT..."

# Check paths exist
if [ ! -f "$HOL_PATH" ]; then
    echo "Error: HOL Light not found at $HOL_PATH"
    exit 1
fi

if [ ! -d "$S2N_BIGNUM_PATH" ]; then
    echo "Error: s2n-bignum directory not found at $S2N_BIGNUM_PATH"
    exit 1
fi

if [ ! -d "$SERVER_PATH" ]; then
    echo "Error: HOL server directory not found at $SERVER_PATH"
    exit 1
fi

# Ensure update_database.ml exists in s2n-bignum directory
if [ ! -f "$S2N_BIGNUM_PATH/update_database.ml" ]; then
    echo "Creating minimal update_database.ml..."
    cat > "$S2N_BIGNUM_PATH/update_database.ml" << 'EOF'
(* Minimal update_database.ml for s2n-bignum compatibility *)
let update_database_dummy = ();;
EOF
    echo "update_database.ml created at $S2N_BIGNUM_PATH/update_database.ml"
fi

# Create setup script with absolute paths
cat > /tmp/hol_setup_simple.ml << EOF
print_endline "Loading HOL Light server with s2n-bignum support...";;
unset_jrh_lexer;;

(* Load threading and Unix support *)
#directory "+threads";;
#directory "+unix";;
#load "unix.cma";;
#load "threads.cma";;

(* Set working directory to s2n-bignum *)
Sys.chdir "$S2N_BIGNUM_PATH";;
print_endline ("Working directory: " ^ Sys.getcwd());;

(* Load s2n-bignum base using loadt instead of needs *)
print_endline "Attempting to load s2n-bignum base...";;
(try
  loadt "arm/proofs/base.ml";;
  print_endline "s2n-bignum base loaded successfully!";;
with
| Sys_error msg -> 
    print_endline ("Warning: Could not load base.ml: " ^ msg);;
    print_endline "Server will start without s2n-bignum base...";;
| e -> 
    print_endline ("Warning: Error loading base.ml: " ^ (Printexc.to_string e));;
    print_endline "Server will start without s2n-bignum base...";;
);;

(* Load the server module *)
print_endline "Loading server module...";;
#mod_use "$SERVER_PATH/server2.ml";;
print_endline "Server module loaded successfully!";;

(* Start the server *)
print_endline "Starting server on port $PORT...";;
set_jrh_lexer;;
Server2.start $PORT;;
EOF

echo "Starting HOL Light with s2n-bignum support..."
echo "HOL Light path: $HOL_PATH"
echo "s2n-bignum path: $S2N_BIGNUM_PATH"
echo "Server path: $SERVER_PATH"

# Start HOL Light from its own directory but with our setup
cd "$(dirname "$HOL_PATH")"
exec bash "$HOL_PATH" < /tmp/hol_setup_simple.ml
