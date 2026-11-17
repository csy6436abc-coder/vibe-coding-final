#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"

KEY="../keypair_linux.pem"
HOST="ec2-user@54.206.154.22"
DIR="/home/ec2-user/agario-game"
OPTS=(-i "$KEY" -o IdentitiesOnly=yes -o StrictHostKeyChecking=accept-new -o LogLevel=ERROR)

ssh "${OPTS[@]}" "$HOST" "mkdir -p $DIR/public"
scp "${OPTS[@]}" package.json server.js "$HOST:$DIR/"
scp "${OPTS[@]}" public/index.html "$HOST:$DIR/public/"
ssh "${OPTS[@]}" "$HOST" "cd $DIR && npm install --omit=dev --no-audit --no-fund && (pm2 restart agario --update-env || pm2 start server.js --name agario) && pm2 save"

echo "Deployed: http://54.206.154.22"
