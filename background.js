// background.js - DealPal background service worker

// Listen to install event
self.addEventListener('install', () => {
  console.log('DealPal background service worker installed');
});

// Listen to activate event
self.addEventListener('activate', () => {
  console.log('DealPal background service worker activated');
});

// Listen for messages from content scripts or popup
chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  if (!message || !message.type) return;

  switch (message.type) {
    case 'PRODUCT_INFO':
      console.log('Received product info:', message.payload);
      // Here you could process product info, e.g., store in local storage
      // Currently just logging
      break;
    default:
      console.warn('Unknown message type in background.js:', message.type);
  }
});
