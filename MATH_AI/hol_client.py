#!/usr/bin/env python3

import socket
import sys
import threading
import time

def read_server_output(sock):
    try:
        while True:
            data = sock.recv(4096).decode('utf-8')
            if not data:
                break
            
            lines = data.strip().split('\n')
            for line in lines:
                if line.startswith('ready:'):
                    print("Server ready for input...")
                elif line.startswith('stdout:'):
                    output = line[7:]
                    if output:
                        try:
                            unescaped = output.encode().decode('unicode_escape')
                            print(f"STDOUT: {unescaped}")
                        except:
                            print(f"STDOUT: {output}")
                elif line.startswith('stderr:'):
                    output = line[7:]
                    if output:
                        try:
                            unescaped = output.encode().decode('unicode_escape')
                            print(f"STDERR: {unescaped}")
                        except:
                            print(f"STDERR: {output}")
                elif line.startswith('result:'):
                    result = line[7:]
                    if result:
                        try:
                            unescaped = result.encode().decode('unicode_escape')
                            print(f"RESULT: {unescaped}")
                        except:
                            print(f"RESULT: {result}")
                elif line.startswith('rerror:'):
                    error = line[7:]
                    try:
                        unescaped = error.encode().decode('unicode_escape')
                        print(f"ERROR: {unescaped}")
                    except:
                        print(f"ERROR: {error}")
                elif line.startswith('info:'):
                    info = line[5:]
                    print(f"INFO: {info}")
                else:
                    print(f"SERVER: {line}")
    except Exception as e:
        print(f"Error reading from server: {e}")

def main():
    host = sys.argv[1] if len(sys.argv) > 1 else "localhost"  # Configuration: server host
    port = int(sys.argv[2]) if len(sys.argv) > 2 else 2012   # Configuration: server port
    
    print(f"Connecting to HOL Light server at {host}:{port}")
    
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((host, port))
        
        reader_thread = threading.Thread(target=read_server_output, args=(sock,))
        reader_thread.daemon = True
        reader_thread.start()
        
        print("Connected! Type OCaml commands (or #quit to exit)")
        print("Examples:")
        print("  2 + 3;;")
        print("  let x = 42;;")
        print("  print_endline \"Hello HOL Light\";;")
        print("  #quit")
        print()
        
        while True:
            try:
                command = input("> ")
                if command.strip() in ["#quit", "quit", "exit"]:
                    sock.send(b"#quit\n")
                    break
                
                sock.send((command + "\n").encode('utf-8'))
                time.sleep(0.1)
                
            except KeyboardInterrupt:
                print("\nSending interrupt to server...")
                sock.send(b"$interrupt\n")
                break
            except EOFError:
                break
                
    except ConnectionRefusedError:
        print(f"Could not connect to server at {host}:{port}")
        print("Make sure the HOL Light server is running!")
        return 1
    except Exception as e:
        print(f"Error: {e}")
        return 1
    finally:
        try:
            sock.close()
        except:
            pass
    
    print("Disconnected from server")
    return 0

if __name__ == "__main__":
    sys.exit(main())
